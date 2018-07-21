ifeq ($(TRAVIS),true)
  BUILD_DIR := $(TRAVIS_BUILD_DIR)
else
  BUILD_DIR := $(dir $(realpath $(lastword $(MAKEFILE_LIST))))../
endif

TARGETS := nostdtest

default: $(TARGETS)
.PHONY: $(TARGETS)

nostdtest:
	cd $(BUILD_DIR)/test/nostdtest && \
	cargo build

clean:
	rm -rf $(BUILD_DIR)/test/*/{Cargo.lock,target/}
