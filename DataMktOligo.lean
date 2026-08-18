module

import AxiomCheck
import DataMktOligo.MuOpt.Main
import DataMktOligo.MuOpt.CstarSpecific
import DataMktOligo.NashInapprox.Main

section
set_option linter.hashCommand false

#check_axioms DataMktOligo.NashInapprox.no_approxNE
#check_axioms DataMktOligo.MuOpt.cStar_specific
#check_axioms DataMktOligo.MuOpt.cStar_le_μ

end
