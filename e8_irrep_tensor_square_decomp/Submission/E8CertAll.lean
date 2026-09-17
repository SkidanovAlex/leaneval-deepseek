import Submission.E8Cert
import Submission.Cert.D0
import Submission.Cert.D1
import Submission.Cert.D2
import Submission.Cert.D3
import Submission.Cert.D4
import Submission.Cert.D5
import Submission.Cert.D6
import Submission.Cert.D7
import Submission.Cert.D8
import Submission.Cert.D9
import Submission.Cert.D10
import Submission.Cert.D11
import Submission.Cert.D12
import Submission.Cert.D13
import Submission.Cert.D14
import Submission.Cert.D15
import Submission.Cert.D16
import Submission.Cert.D17
import Submission.Cert.D18
import Submission.Cert.D19
import Submission.Cert.D20
import Submission.Cert.D21
import Submission.Cert.D22
import Submission.Cert.D23
import Submission.Cert.D24
import Submission.Cert.D25
import Submission.Cert.D26
import Submission.Cert.D27
import Submission.Cert.D28
import Submission.Cert.D29
import Submission.Cert.D30
import Submission.Cert.D31
import Submission.Cert.D32
import Submission.Cert.D33
import Submission.Cert.D34
import Submission.Cert.D35
import Submission.Cert.D36
import Submission.Cert.D37
import Submission.Cert.D38
import Submission.Cert.D39

/-!
# The c-table certificate, assembled

The certificates live in the per-weight chunks `Submission.Cert.D<d>`, one file per `d` (a single
`decide` over all `19200` terms exceeds the memory cap), and are glued back together here.
-/

set_option maxHeartbeats 0
set_option maxRecDepth 1000000
set_option linter.unusedVariables false

noncomputable section
namespace Submission.E8Cert

open Submission.E8Extract Submission.E8Orbit Submission.E8Character Submission.E8Casimir
open Submission.E8Enum Submission.E8Numerics Submission.E8Engine
open Submission.WeylReflect Submission.WeylWeights

/-- **The c-table certificate**: the dominant conjugate of every term `ord40 d + (k+1) * pR j` is
the tabulated weight `ord40 (sidTab d j k)`, or is outside the forty weights. -/
theorem cert_sid (d : Fin 40) (j : Fin 120) (k : Fin 4) :
    domIdx (term d j k)
      = (if h : sidTab d j k < 40 then some ⟨sidTab d j k, h⟩ else none) := by
  fin_cases d
  · exact cert_sid_0 j k
  · exact cert_sid_1 j k
  · exact cert_sid_2 j k
  · exact cert_sid_3 j k
  · exact cert_sid_4 j k
  · exact cert_sid_5 j k
  · exact cert_sid_6 j k
  · exact cert_sid_7 j k
  · exact cert_sid_8 j k
  · exact cert_sid_9 j k
  · exact cert_sid_10 j k
  · exact cert_sid_11 j k
  · exact cert_sid_12 j k
  · exact cert_sid_13 j k
  · exact cert_sid_14 j k
  · exact cert_sid_15 j k
  · exact cert_sid_16 j k
  · exact cert_sid_17 j k
  · exact cert_sid_18 j k
  · exact cert_sid_19 j k
  · exact cert_sid_20 j k
  · exact cert_sid_21 j k
  · exact cert_sid_22 j k
  · exact cert_sid_23 j k
  · exact cert_sid_24 j k
  · exact cert_sid_25 j k
  · exact cert_sid_26 j k
  · exact cert_sid_27 j k
  · exact cert_sid_28 j k
  · exact cert_sid_29 j k
  · exact cert_sid_30 j k
  · exact cert_sid_31 j k
  · exact cert_sid_32 j k
  · exact cert_sid_33 j k
  · exact cert_sid_34 j k
  · exact cert_sid_35 j k
  · exact cert_sid_36 j k
  · exact cert_sid_37 j k
  · exact cert_sid_38 j k
  · exact cert_sid_39 j k

/-- The `brk` values of the surviving terms agree with the table. -/
theorem brk_eq (d : Fin 40) (j : Fin 120) (k : Fin 4) (h : sidTab d j k < 40) :
    brkF (term d j k) j = brkTab d j k := by
  fin_cases d
  · exact brk_eq_0 j k h
  · exact brk_eq_1 j k h
  · exact brk_eq_2 j k h
  · exact brk_eq_3 j k h
  · exact brk_eq_4 j k h
  · exact brk_eq_5 j k h
  · exact brk_eq_6 j k h
  · exact brk_eq_7 j k h
  · exact brk_eq_8 j k h
  · exact brk_eq_9 j k h
  · exact brk_eq_10 j k h
  · exact brk_eq_11 j k h
  · exact brk_eq_12 j k h
  · exact brk_eq_13 j k h
  · exact brk_eq_14 j k h
  · exact brk_eq_15 j k h
  · exact brk_eq_16 j k h
  · exact brk_eq_17 j k h
  · exact brk_eq_18 j k h
  · exact brk_eq_19 j k h
  · exact brk_eq_20 j k h
  · exact brk_eq_21 j k h
  · exact brk_eq_22 j k h
  · exact brk_eq_23 j k h
  · exact brk_eq_24 j k h
  · exact brk_eq_25 j k h
  · exact brk_eq_26 j k h
  · exact brk_eq_27 j k h
  · exact brk_eq_28 j k h
  · exact brk_eq_29 j k h
  · exact brk_eq_30 j k h
  · exact brk_eq_31 j k h
  · exact brk_eq_32 j k h
  · exact brk_eq_33 j k h
  · exact brk_eq_34 j k h
  · exact brk_eq_35 j k h
  · exact brk_eq_36 j k h
  · exact brk_eq_37 j k h
  · exact brk_eq_38 j k h
  · exact brk_eq_39 j k h

/-- The grouped c-table agrees with the tabulated c-table of `Submission.E8Extract`. -/
theorem ctab_eq (d e : Fin 40) : ctab d e = ctabN d e := by
  fin_cases d
  · exact ctab_eq_0 e
  · exact ctab_eq_1 e
  · exact ctab_eq_2 e
  · exact ctab_eq_3 e
  · exact ctab_eq_4 e
  · exact ctab_eq_5 e
  · exact ctab_eq_6 e
  · exact ctab_eq_7 e
  · exact ctab_eq_8 e
  · exact ctab_eq_9 e
  · exact ctab_eq_10 e
  · exact ctab_eq_11 e
  · exact ctab_eq_12 e
  · exact ctab_eq_13 e
  · exact ctab_eq_14 e
  · exact ctab_eq_15 e
  · exact ctab_eq_16 e
  · exact ctab_eq_17 e
  · exact ctab_eq_18 e
  · exact ctab_eq_19 e
  · exact ctab_eq_20 e
  · exact ctab_eq_21 e
  · exact ctab_eq_22 e
  · exact ctab_eq_23 e
  · exact ctab_eq_24 e
  · exact ctab_eq_25 e
  · exact ctab_eq_26 e
  · exact ctab_eq_27 e
  · exact ctab_eq_28 e
  · exact ctab_eq_29 e
  · exact ctab_eq_30 e
  · exact ctab_eq_31 e
  · exact ctab_eq_32 e
  · exact ctab_eq_33 e
  · exact ctab_eq_34 e
  · exact ctab_eq_35 e
  · exact ctab_eq_36 e
  · exact ctab_eq_37 e
  · exact ctab_eq_38 e
  · exact ctab_eq_39 e

end Submission.E8Cert
