import BinPack.NextFit
import BinPack.FirstFit
import BinPack.Harmonic
import AxiomCheck

section
set_option linter.hashCommand false

#check_axioms nextFit_isPacking
#check_axioms nextFit_ratio
#check_axioms harmonicPack_isPacking
#check_axioms harmonicPack_ratio

end
