.PHONY: all test clean parser check-dependencies macos_sip_fix

MILL = ./mill

WEMELT_JAVA = wemelt/src/wemelt/Parser.java \
            wemelt/src/wemelt/Scanner.java

WEMELT_JAR = out/wemelt/jar/dest/out.jar
WEMELT_LAUNCHER = ./out/wemelt/launcher/dest/run
WEMELT_SH  = ./wemelt.sh

all: parser $(WEMELT_JAR) $(WEMELT_SH)  macos_sip_fix

parser: $(WEMELT_JAVA)

clean:
	$(MILL) clean
	rm -f $(WEMELT_JAVA)
	rm -f $(WEMELT_SH)

check-dependencies:
	$(MILL) mill.scalalib.Dependency/updates

$(WEMELT_LAUNCHER):
	@echo $@
	$(MILL) wemelt.launcher

$(WEMELT_JAR):
	@echo $@
	$(MILL) wemelt.jar

$(WEMELT_SH): $(WEMELT_LAUNCHER)
	@echo "[echo]  $@"; echo "#!/usr/bin/env bash" > $@; echo "export LD_LIBRARY_PATH=$(PWD)/wemelt/lib" >> $@; echo "source $(WEMELT_LAUNCHER)" >> $@
	@echo "[chmod] $@"; chmod +x $@

%.java: %.grammar
	java -jar beaver.jar -t $^

%.java: %.flex
	jflex -nobak $^

o: $(WEMELT_OBJ)
	@echo $(WEMELT_OBJ)

macos_sip_fix: wemelt/lib/libz3java.dylib wemelt/lib/libz3.dylib
	@if [ $$(uname -s) = "Darwin" ];  then \
	    make -s libz3java.dylib libz3.dylib; \
	 fi

lib%.dylib: wemelt/lib/lib%.dylib
	ln -s $<
