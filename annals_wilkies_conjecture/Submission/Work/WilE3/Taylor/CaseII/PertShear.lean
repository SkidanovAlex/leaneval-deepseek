import Mathlib
import Submission.Work.WilE3.Taylor.CaseII.Defs
import Submission.Work.WilE3.Taylor.Grad.PolarDefs
import Submission.Work.WilE3.eaEval_analytic

/-!
  annals_wilkies_conjecture, AREA E3 / Taylor / CaseII: **the shear description of the perturbed
  polar minors** (the algebraic input of the node T4 `pertSys_det_ne` of
  `cbc/wilkies_e3_caseII.md`).

  With `G = sqGrad c Φ = ∑ₗ (∂ₗΦ)²` and `Dᵢ = ∂ᵢΦ`, the perturbed polar minor
  `pertMinor c Φ v i₀ i = D_{i₀}(∂ᵢG + vᵢG) − Dᵢ(∂_{i₀}G + v_{i₀}G)` can be written, on the open
  set `Ush = {G · D_{i₀} ≠ 0}`, as

      `pertMinor(v)ᵢ = G · D_{i₀} · (aᵢ + bᵢ · v_{i₀} + vᵢ)`

  where `aᵢ = (D_{i₀}∂ᵢG − Dᵢ∂_{i₀}G)/(G D_{i₀})` and `bᵢ = −Dᵢ/D_{i₀}`.  This is the *shear form*
  of the system: the parameter `vᵢ` enters the `i`-th equation with coefficient `1` and the parameter
  `v_{i₀}` enters every equation through a single `b`.  It is what turns the parametric
  transversality into equal-dimension Sard (`Work.WilE3.Taylor.CaseII.shear_regular_ae`).
-/

set_option autoImplicit false
noncomputable section
open Classical Topology Filter
open WilkiesDesign.E

namespace Work.WilE3.Taylor.CaseII

variable {k r : ℕ}

/-- The common denominator `G · ∂_{i₀}Φ` of the shear description, `G = sqGrad c Φ`. -/
def denP (c : EAChain k r) (Φ : EAPoly k r) (i₀ : Fin k) : EAPoly k r :=
  sqGrad c Φ * eaD c i₀ Φ

/-- Numerator of the shear coefficient `a`: `∂_{i₀}Φ ∂ᵢG − ∂ᵢΦ ∂_{i₀}G`, `G = sqGrad c Φ`. -/
def aNumP (c : EAChain k r) (Φ : EAPoly k r) (i₀ i : Fin k) : EAPoly k r :=
  eaD c i₀ Φ * eaD c i (sqGrad c Φ) - eaD c i Φ * eaD c i₀ (sqGrad c Φ)

/-- Numerator of the shear coefficient `b`: `−∂ᵢΦ · G`, `G = sqGrad c Φ`. -/
def bNumP (c : EAChain k r) (Φ : EAPoly k r) (i : Fin k) : EAPoly k r :=
  -(eaD c i Φ * sqGrad c Φ)

/-- The open set on which the shear description of the perturbed polar minors is valid:
`{x | G x · ∂_{i₀}Φ x ≠ 0}`. -/
def Ush (c : EAChain k r) (Φ : EAPoly k r) (i₀ : Fin k) : Set (Fin k → ℝ) :=
  {x | eaEval c (denP c Φ i₀) x ≠ 0}

/-- The shear coefficient `a` of the perturbed polar minor (junk in slot `i₀`, where it is never
used). -/
def aSh (c : EAChain k r) (Φ : EAPoly k r) (i₀ : Fin k) : (Fin k → ℝ) → (Fin k → ℝ) :=
  fun x i => if i = i₀ then 0 else eaEval c (aNumP c Φ i₀ i) x / eaEval c (denP c Φ i₀) x

/-- The shear coefficient `b` of the perturbed polar minor (junk in slot `i₀`, where it is never
used). -/
def bSh (c : EAChain k r) (Φ : EAPoly k r) (i₀ : Fin k) : (Fin k → ℝ) → (Fin k → ℝ) :=
  fun x i => if i = i₀ then 0 else eaEval c (bNumP c Φ i) x / eaEval c (denP c Φ i₀) x

/-- `aNumP` is `pertMinor` at `v = 0`. -/
lemma aNumP_eq_pertMinor (c : EAChain k r) (Φ : EAPoly k r) (i₀ i : Fin k) :
    aNumP c Φ i₀ i = pertMinor c Φ (fun _ => 0) i₀ i := by
  simp [aNumP, pertMinor]

/-- `Ush` is open (it is the complement of a zero set of a continuous function). -/
lemma isOpen_Ush (c : EAChain k r) (Φ : EAPoly k r) (i₀ : Fin k) : IsOpen (Ush c Φ i₀) :=
  isOpen_compl_singleton.preimage
    (continuous_iff_continuousAt.mpr fun x => (eaEval_analytic c _ x).continuousAt)

/-! ### Expansion lemmas -/

lemma eaEval_denP (c : EAChain k r) (Φ : EAPoly k r) (i₀ : Fin k) (x : Fin k → ℝ) :
    eaEval c (denP c Φ i₀) x = eaEval c (sqGrad c Φ) x * eaEval c (eaD c i₀ Φ) x := by
  simp [denP, eaEval]

lemma eaEval_aNumP (c : EAChain k r) (Φ : EAPoly k r) (i₀ i : Fin k) (x : Fin k → ℝ) :
    eaEval c (aNumP c Φ i₀ i) x
      = eaEval c (eaD c i₀ Φ) x * eaEval c (eaD c i (sqGrad c Φ)) x
        - eaEval c (eaD c i Φ) x * eaEval c (eaD c i₀ (sqGrad c Φ)) x := by
  simp [aNumP, eaEval]

lemma eaEval_bNumP (c : EAChain k r) (Φ : EAPoly k r) (i : Fin k) (x : Fin k → ℝ) :
    eaEval c (bNumP c Φ i) x = -(eaEval c (eaD c i Φ) x * eaEval c (sqGrad c Φ) x) := by
  simp [bNumP, eaEval]

lemma eaEval_pertMinor (c : EAChain k r) (Φ : EAPoly k r) (v : Fin k → ℝ) (i₀ i : Fin k)
    (x : Fin k → ℝ) :
    eaEval c (pertMinor c Φ v i₀ i) x =
      eaEval c (eaD c i₀ Φ) x * (eaEval c (eaD c i (sqGrad c Φ)) x + v i * eaEval c (sqGrad c Φ) x)
        - eaEval c (eaD c i Φ) x *
            (eaEval c (eaD c i₀ (sqGrad c Φ)) x + v i₀ * eaEval c (sqGrad c Φ) x) := by
  simp [pertMinor, eaEval]

/-- The shear values of `aSh` and `bSh`. -/
lemma aSh_apply_of_ne (c : EAChain k r) (Φ : EAPoly k r) (i₀ : Fin k) (x : Fin k → ℝ)
    {i : Fin k} (hi : i ≠ i₀) :
    aSh c Φ i₀ x i = eaEval c (aNumP c Φ i₀ i) x / eaEval c (denP c Φ i₀) x := by
  simp [aSh, hi]

lemma bSh_apply_of_ne (c : EAChain k r) (Φ : EAPoly k r) (i₀ : Fin k) (x : Fin k → ℝ)
    {i : Fin k} (hi : i ≠ i₀) :
    bSh c Φ i₀ x i = eaEval c (bNumP c Φ i) x / eaEval c (denP c Φ i₀) x := by
  simp [bSh, hi]

/-- **The shear identity**: on `Ush` the perturbed polar minor is the denominator times the shear
expression, `pertMinor(v)ᵢ = G·D_{i₀}·(aᵢ + bᵢ·v_{i₀} + vᵢ)`. -/
lemma aSh_add_bSh_mul_add (c : EAChain k r) (Φ : EAPoly k r) (i₀ : Fin k) (v : Fin k → ℝ)
    (x : Fin k → ℝ) (hx : x ∈ Ush c Φ i₀) (i : Fin k) (hi : i ≠ i₀) :
    aSh c Φ i₀ x i + bSh c Φ i₀ x i * v i₀ + v i
      = eaEval c (pertMinor c Φ v i₀ i) x / eaEval c (denP c Φ i₀) x := by
  have hd : eaEval c (denP c Φ i₀) x ≠ 0 := hx
  have hd' : eaEval c (sqGrad c Φ) x * eaEval c (eaD c i₀ Φ) x ≠ 0 := by
    rw [← eaEval_denP]; exact hd
  obtain ⟨hdG, hdD⟩ := mul_ne_zero_iff.mp hd'
  rw [aSh_apply_of_ne c Φ i₀ x hi, bSh_apply_of_ne c Φ i₀ x hi, eaEval_denP, eaEval_aNumP,
    eaEval_bNumP, eaEval_pertMinor]
  field_simp
  ring

end Work.WilE3.Taylor.CaseII
