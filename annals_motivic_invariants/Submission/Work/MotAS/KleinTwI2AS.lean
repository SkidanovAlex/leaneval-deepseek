import Mathlib
import Submission.Work.MotAS.ASData
import Submission.Work.MotAS.KleinTwI2ASGuide
import Submission.Work.MotAS.ASTransport
import Submission.Work.MotAS.ASTransportR
import Submission.Work.MotAS.asTransportSD
import Submission.Work.MotAS.ASMatrix
import Submission.Work.MotAS.ASRul.I2

set_option linter.unusedVariables false -- v435-speed

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.MotAS

/-- **I2^AS** — the transported split identity `P^AS ∘ R^AS = s'^AS • id`.

This used to be an open node (`Work.MotAS.KleinTwI2AS` is named in
`Submission/Work/MotAS/KleinTwI34ASGuide.lean` and in
`Submission/Work/MotC5N3/censusAS2_class_sdual.lean`); it is now a one-line consequence of
`Work.MotAS.ASRul.I2` (`Submission/Work/MotAS/ASRul/I2.lean`), which proves exactly this identity
with the two arguments `h5` and `z` interchanged.  The transports it uses (`asTransportP`,
`asTransportR`, `asTransportSD`) are the proved ones of `ASTransport`, `ASTransportR` and
`asTransportSD`, so nothing new is needed. -/
theorem KleinTwI2AS {R : Type*} [CommRing R] (a b g : R) (z : Fin 5 → R) (h5 : (5 : R) = 0) :
    kleinPAS a b g (kleinRAS a b g z) = fun i => kleinSecDualAS a b g z * z i :=
  Work.MotAS.ASRul.I2 a b g h5 z

end Work.MotAS
