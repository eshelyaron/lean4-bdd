BDD_LEAN_FILES := $(wildcard Bdd/*.lean)

BASE = https://eshelyaron.com/lean4-bdd/docs/Bdd/

dependencies.svg: dependencies.dot
	dot -Tsvg dependencies.dot > $@

dependencies.dot: $(BDD_LEAN_FILES)
	@echo "digraph {" > $@
	@$(foreach file, $^ ,\
		if grep -q "sorry" "$(file)"; then \
			echo "$(basename $(notdir $(file))) [ label = \"$(basename $(notdir $(file)))\", color="red", href = \"$(BASE)$(basename $(notdir $(file))).html\" ]" >> $@; \
		else \
			echo "$(basename $(notdir $(file))) [ label = \"$(basename $(notdir $(file)))\", color="green", href = \"$(BASE)$(basename $(notdir $(file))).html\" ]" >> $@; \
		fi;)
	@(grep -nr "import Bdd" Bdd/*.lean | awk -F '[./]' '{print $$4 " -> " $$2}') >> $@
	@echo "}" >> $@
