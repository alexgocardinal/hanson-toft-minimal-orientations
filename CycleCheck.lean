import HansonToft

namespace HansonToft

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem cycleFiniteCheck_eq_true : cycleFiniteCheck = true := by
  decide

#print axioms cycleFiniteCheck_eq_true

end HansonToft
