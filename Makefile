.PHONY: all test clean parser check-dependencies macos_sip_fix

MILL = ./mill

TOOL_JAVA = tool/src/tool/Parser.java \
            tool/src/tool/Scanner.java

CC ?= cc
CFLAGS ?= -Iinclude -Wall -W -Wpedantic

TOOL_JAR = out/tool/jar/dest/out.jar
TOOL_LAUNCHER = ./out/tool/launcher/dest/run
TOOL_SH  = ./armlogictool.sh

all: $(TOOL_JAR) $(TOOL_SH) macos_sip_fix

parser: $(TOOL_JAVA)

clean:
	$(MILL) clean
	rm -f $(TOOL_SH)

check-dependencies:
	$(MILL) mill.scalalib.Dependency/updates

$(TOOL_LAUNCHER):
	@echo $@
	$(MILL) tool.launcher

$(TOOL_JAR):
	@echo $@
	$(MILL) tool.jar

$(TOOL_SH): $(TOOL_LAUNCHER)
	@echo "[echo]  $@"; echo "#!/usr/bin/env bash" > $@; echo "export LD_LIBRARY_PATH=$(PWD)/tool/lib" >> $@; echo "source $(TOOL_LAUNCHER)" >> $@
	@echo "[chmod] $@"; chmod +x $@

%.java: %.grammar
	java -jar beaver.jar -t $^

%.java: %.flex
	jflex -nobak $^

o: $(TOOL_OBJ)
	@echo $(TOOL_OBJ)

macos_sip_fix: tool/lib/libz3java.dylib tool/lib/libz3.dylib
	@if [ $$(uname -s) = "Darwin" ];  then \
	    make -s libz3java.dylib libz3.dylib; \
	 fi

lib%.dylib: tool/lib/lib%.dylib
	ln -s $<
