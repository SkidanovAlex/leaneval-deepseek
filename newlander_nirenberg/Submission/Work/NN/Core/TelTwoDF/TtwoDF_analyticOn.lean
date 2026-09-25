import Mathlib
import Submission.Work.CR.Flat.Polydisc
import Submission.Work.NN.Core.CnPert
import Submission.Work.NN.Core.TelTwoDF.Setup
import Submission.Work.NN.Core.TelTwoDF.Defs
import Submission.Work.NN.Core.TelTwoDF.Rec
import Submission.Work.NN.Core.TelTwoDF.Rec2
import Submission.Work.NN.Core.TelTwoDF.Solves
import Submission.Work.NN.Core.TelTwoDF.ContDiffRec
import Submission.Work.NN.Core.TelTwoDF.analyticOn_cauchyTransform_disc
import Submission.Work.NN.Core.TelTwoDF.analyticOn_integral_compact
import Submission.Work.NN.Core.TelTwoDF.dbarTransform_eq_ball
import Submission.Work.NN.Core.TelTwoDF.analyticOn_integral_disc_tsupport
import Submission.Work.NN.Core.TelTwoDF.exists_analytic_holomorphic_dbar_split
import Submission.Work.NN.Core.TelTwoDF.analyticOn_of_iteratedFDeriv_le_factorial
import Submission.Work.NN.Core.TelTwoDF.analyticOn_dbarTransform_dbarC_sharpCut_mul
import Submission.Work.NN.Core.TelTwoDF.analyticOn_dbarTransform_sharpCut_mul

namespace Work.NN.Core.TelTwoDF

open scoped NNReal ENNReal ContDiff
open Set

variable {n : ℕ}

/-! ## The stage radii of the induction

The induction of `TtwoDF_analyticOn` tracks the stage-`m` data on the polydisc `polydisc 0 (rad m)`,
where the `k`-th radius is `ρ' k + (G.a k - ρ' k) * fac m` as long as `k < m` and equals
`G.b k + (Cdat k - G.b k) * gp m` afterwards.  The radii are chosen so that

* `rad 0 k < Cdat k` (the cut-off `χ` equals `1` on the first polydisc),
* `rad (m+1) k < rad m k` for every `k` (the polydiscs are strictly nested), and
* `rad (m+1) m < G.a m` (the cut-off `kappa G m` equals `1` on the `(m+1)`-st polydisc). -/

/-- The interpolation factor `fac m = 1 - m/(n+1)` of the `m`-th stage. -/
noncomputable def fac (n m : ℕ) : ℝ := 1 - (m : ℝ) / ((n : ℝ) + 1)

lemma fac_le_one (n m : ℕ) : fac n m ≤ 1 := by
  rw [fac]
  have h : 0 ≤ (m : ℝ) / ((n : ℝ) + 1) := by positivity
  linarith

lemma fac_pos {m : ℕ} (hm : m ≤ n) : 0 < fac n m := by
  rw [fac]
  have hm' : (m : ℝ) < (n : ℝ) + 1 := by
    have h : (m : ℝ) ≤ (n : ℝ) := by exact_mod_cast hm
    linarith
  have h : (m : ℝ) / ((n : ℝ) + 1) < 1 := by
    rw [div_lt_one (by positivity)]
    exact hm'
  linarith

lemma fac_nonneg {m : ℕ} (hm : m ≤ n) : 0 ≤ fac n m := (fac_pos hm).le

lemma fac_succ_lt (n m : ℕ) : fac n (m + 1) < fac n m := by
  rw [fac, fac]
  have h : ((m + 1 : ℕ) : ℝ) = (m : ℝ) + 1 := by push_cast; ring
  rw [h]
  have h1 : (0 : ℝ) < 1 / ((n : ℝ) + 1) := by positivity
  have h2 : ((m : ℝ) + 1) / ((n : ℝ) + 1) = (m : ℝ) / ((n : ℝ) + 1) + 1 / ((n : ℝ) + 1) :=
    add_div _ _ _
  rw [h2]
  linarith

/-- The fraction `gp m = 1/(m+2)` of the "outer" stage radii. -/
noncomputable def gp (m : ℕ) : ℝ := 1 / ((m : ℝ) + 2)

lemma gp_pos (m : ℕ) : 0 < gp m := by rw [gp]; positivity

lemma gp_lt_one (m : ℕ) : gp m < 1 := by
  rw [gp, div_lt_one (by positivity)]
  have h : (0 : ℝ) ≤ (m : ℝ) := Nat.cast_nonneg m
  linarith

lemma gp_succ_lt (m : ℕ) : gp (m + 1) < gp m := by
  rw [gp, gp]
  have h : ((m + 1 : ℕ) : ℝ) + 2 = (m : ℝ) + 3 := by push_cast; ring
  rw [h]
  exact one_div_lt_one_div_of_lt (by positivity) (by linarith)

/-- The multi-radius of the polydisc on which the data at stage `m` of the parameterised
telescoping are tracked. -/
noncomputable def rad (G : Geom n) (Cdat ρ' : Fin n → ℝ) (m : ℕ) (k : Fin n) : ℝ :=
  if (k : ℕ) < m then ρ' k + (G.a k - ρ' k) * fac n m
  else G.b k + (Cdat k - G.b k) * gp m

lemma rad_of_lt {G : Geom n} {Cdat ρ' : Fin n → ℝ} {m : ℕ} {k : Fin n} (h : (k : ℕ) < m) :
    rad G Cdat ρ' m k = ρ' k + (G.a k - ρ' k) * fac n m := by
  rw [rad, if_pos h]

lemma rad_of_le {G : Geom n} {Cdat ρ' : Fin n → ℝ} {m : ℕ} {k : Fin n} (h : m ≤ (k : ℕ)) :
    rad G Cdat ρ' m k = G.b k + (Cdat k - G.b k) * gp m := by
  rw [rad, if_neg (not_lt.mpr h)]

lemma rad_zero (G : Geom n) (Cdat ρ' : Fin n → ℝ) (k : Fin n) :
    rad G Cdat ρ' 0 k = G.b k + (Cdat k - G.b k) * gp 0 :=
  rad_of_le (Nat.zero_le _)

/-- At its own stage, the `s`-th radius is the "outer" value. -/
lemma rad_self {G : Geom n} {Cdat ρ' : Fin n → ℝ} (s : Fin n) :
    rad G Cdat ρ' (s : ℕ) s = G.b s + (Cdat s - G.b s) * gp (s : ℕ) :=
  rad_of_le le_rfl

lemma rad_succ_self {G : Geom n} {Cdat ρ' : Fin n → ℝ} (s : Fin n) :
    rad G Cdat ρ' ((s : ℕ) + 1) s = ρ' s + (G.a s - ρ' s) * fac n ((s : ℕ) + 1) :=
  rad_of_lt (Nat.lt_succ_self (s : ℕ))

lemma rad_lt_a {G : Geom n} {Cdat ρ' : Fin n → ℝ} (s : Fin n)
    (hρ'e : ∀ j, ρ' j < G.e j) : rad G Cdat ρ' ((s : ℕ) + 1) s < G.a s := by
  rw [rad_succ_self]
  have h1 : fac n ((s : ℕ) + 1) < 1 := by
    rw [fac]
    have h : 0 < (((s : ℕ) + 1 : ℕ) : ℝ) / ((n : ℝ) + 1) := by positivity
    linarith
  have h2 : 0 < G.a s - ρ' s := by
    have h3 := hρ'e s
    have h4 := G.hea s
    linarith
  have h3 : (G.a s - ρ' s) * fac n ((s : ℕ) + 1) < (G.a s - ρ' s) * 1 :=
    mul_lt_mul_of_pos_left h1 h2
  linarith

lemma rad_pos {G : Geom n} {Cdat ρ' : Fin n → ℝ} (hbC : ∀ j, G.b j < Cdat j)
    (hρ' : ∀ j, 0 < ρ' j) (hρ'e : ∀ j, ρ' j < G.e j) {m : ℕ} (hm : m ≤ n) (k : Fin n) :
    0 < rad G Cdat ρ' m k := by
  rcases lt_or_ge ((k : ℕ)) m with h | h
  · rw [rad_of_lt h]
    have h2 : 0 < G.a k - ρ' k := by
      have h3 := hρ'e k
      have h4 := G.hea k
      linarith
    have h4 : 0 < (G.a k - ρ' k) * fac n m := mul_pos h2 (fac_pos hm)
    linarith [hρ' k]
  · rw [rad_of_le h]
    have hb := G.b_pos k
    have hc : 0 < Cdat k := lt_trans hb (hbC k)
    have hconv : G.b k + (Cdat k - G.b k) * gp m = gp m * Cdat k + (1 - gp m) * G.b k := by ring
    rw [hconv]
    have h1 : 0 < gp m * Cdat k := mul_pos (gp_pos m) hc
    have h2 : 0 ≤ (1 - gp m) * G.b k := mul_nonneg (by linarith [(gp_lt_one m).le]) hb.le
    linarith

lemma rad_mono {G : Geom n} {Cdat ρ' : Fin n → ℝ} (hbC : ∀ j, G.b j < Cdat j)
    (hρ'e : ∀ j, ρ' j < G.e j) (m : ℕ) (k : Fin n) :
    rad G Cdat ρ' (m + 1) k < rad G Cdat ρ' m k := by
  rcases lt_trichotomy ((k : ℕ)) m with h | h | h
  · have hkm : (k : ℕ) < m + 1 := by omega
    rw [rad_of_lt hkm, rad_of_lt h]
    have h1 : 0 < G.a k - ρ' k := by
      have h3 := hρ'e k
      have h4 := G.hea k
      linarith
    have h3 : (G.a k - ρ' k) * fac n (m + 1) < (G.a k - ρ' k) * fac n m :=
      mul_lt_mul_of_pos_left (fac_succ_lt n m) h1
    linarith
  · have hkm : (k : ℕ) < m + 1 := by omega
    have hmk : m ≤ (k : ℕ) := by omega
    rw [rad_of_lt hkm, rad_of_le hmk]
    have h1 : 0 < G.a k - ρ' k := by
      have h3 := hρ'e k
      have h4 := G.hea k
      linarith
    have h2 : fac n (m + 1) < 1 := by
      rw [fac]
      have h : 0 < (((m + 1 : ℕ)) : ℝ) / ((n : ℝ) + 1) := by positivity
      linarith
    have h3 : ρ' k + (G.a k - ρ' k) * fac n (m + 1) < G.a k := by
      have h4 : (G.a k - ρ' k) * fac n (m + 1) < (G.a k - ρ' k) * 1 :=
        mul_lt_mul_of_pos_left h2 h1
      linarith
    have h5 : G.a k < G.b k := G.hab k
    have h6 : G.b k < G.b k + (Cdat k - G.b k) * gp m := by
      have h7 : 0 < Cdat k - G.b k := by have := hbC k; linarith
      have h8 : 0 < (Cdat k - G.b k) * gp m := mul_pos h7 (gp_pos m)
      linarith
    linarith
  · have hkm : m + 1 ≤ (k : ℕ) := by omega
    have hmk : m ≤ (k : ℕ) := by omega
    rw [rad_of_le hkm, rad_of_le hmk]
    have h1 : 0 < Cdat k - G.b k := by have := hbC k; linarith
    have h3 : (Cdat k - G.b k) * gp (m + 1) < (Cdat k - G.b k) * gp m :=
      mul_lt_mul_of_pos_left (gp_succ_lt m) h1
    linarith

lemma rho_lt_rad {G : Geom n} {Cdat ρ' : Fin n → ℝ} (hbC : ∀ j, G.b j < Cdat j)
    (hρ'e : ∀ j, ρ' j < G.e j) {m : ℕ} (hm : m ≤ n) (k : Fin n) :
    ρ' k < rad G Cdat ρ' m k := by
  rcases lt_or_ge ((k : ℕ)) m with h | h
  · rw [rad_of_lt h]
    have h1 : 0 < G.a k - ρ' k := by
      have h3 := hρ'e k
      have h4 := G.hea k
      linarith
    have h2 : 0 < (G.a k - ρ' k) * fac n m := mul_pos h1 (fac_pos hm)
    linarith
  · rw [rad_of_le h]
    have h1 : ρ' k < G.e k := hρ'e k
    have h2 : G.e k < G.a k := G.hea k
    have h3 : G.a k < G.b k := G.hab k
    have h4 : G.b k < Cdat k := hbC k
    have h5 : 0 ≤ (Cdat k - G.b k) * gp m := mul_nonneg (by linarith) (gp_pos m).le
    linarith

lemma rad_zero_lt_Cdat {G : Geom n} {Cdat ρ' : Fin n → ℝ} (hbC : ∀ j, G.b j < Cdat j)
    (k : Fin n) : rad G Cdat ρ' 0 k < Cdat k := by
  rw [rad_zero]
  have h : 0 < Cdat k - G.b k := by have := hbC k; linarith
  have h2 : (Cdat k - G.b k) * gp 0 < (Cdat k - G.b k) * 1 :=
    mul_lt_mul_of_pos_left (gp_lt_one 0) h
  linarith

/-- Real analyticity of the parameterised telescoping on analytic data.

`TtwoDF G χ η = S2 G (chiMul χ η)` is real analytic on `polydisc 0 ρ'` whenever `η` is real
analytic on `polydisc 0 ρ`, where `χ` is a bump equal to `1` on `polydisc 0 Cdat` with support in
`polydisc 0 ρ`, and `G` is the geometry of the telescoping with `G.b < Cdat < ρ`.

Proof sketch. `η̃ := chiMul χ η` is analytic on `polydisc 0 Cdat` (as `χ = 1` there) and globally
smooth.  Track the stages `D^m := uD G η̃ m` on the polydiscs of radius
`rad m k := if (k:ℕ) < m then ρ' k + (G.a k - ρ' k) * (1 - m/(n+1)) else (G.b k + Cdat k)/2`
and show by induction on `m` that `D^m i l` is analytic on `polydisc 0 (rad m)`.  At stage `s`
the factor `1 - kappa G s` vanishes on `polydisc 0 (rad (s+1))` (as `rad (s+1) s < G.a s`), so
the `(0,2)`-stage reduces to the transform `TL G s (kappabar G s * D^s i l)`, whose integrand is
supported in the annulus `G.a s ≤ ‖ζ‖ ≤ G.b s`, away from the pole `ζ = z s`
(`‖z s‖ < G.a s`): use `TL_eq`, `dbarTransform_eq_ball` (pole form) and the parameter integral
lemma `analyticOn_integral_disc_tsupport`.  The final output
`uPsi G η̃ s l = TL G s (kappa G s * D^s s l)`, rewritten in the same pole form, splits with
`kappa G s = 1_{‖ζ‖ ≤ G.a s} + (kappa G s - 1_{‖ζ‖ ≤ G.a s})` into the truncated Cauchy transform
of `D^s s l` over the disc of radius `G.a s` (analyticity by `analyticOn_cauchyTransform_disc`,
applicable since `G.a s < rad s s = (G.b s + Cdat s)/2`) plus a summand supported in the annulus
`G.a s ≤ ‖ζ‖ ≤ G.b s` (analyticity by `analyticOn_integral_compact`).  Then
`S2 G η̃ j = ∑ s, uPsi G η̃ s j` is a finite sum of functions analytic on `polydisc 0 ρ'`
(as `ρ' k < rad n k`).

Implementation.  The radii used below are
`rad m k = ρ' k + (G.a k - ρ' k)·(1 - m/(n+1))` for `k < m`, and
`rad m k = G.b k + (Cdat k - G.b k)/(m+2)` for `k ≥ m`; they satisfy
`rad 0 k < Cdat k`, `rad (m+1) k < rad m k` and `rad (m+1) m < G.a m`.
The two analytic inputs are the delegated lemmas
`Work.NN.Core.TelTwoDF.analyticOn_dbarTransform_dbarC_sharpCut_mul` (the `(0,2)`-stage, pole-free)
and `Work.NN.Core.TelTwoDF.analyticOn_dbarTransform_sharpCut_mul` (the final output, where the
pole `ζ = z s` lies in the support of the weight `kappa G s`). -/
theorem TtwoDF_analyticOn {n : ℕ} {ρ ρ' : Fin n → ℝ} (hlt : ∀ j, ρ' j < ρ j)
    (hρ : ∀ j, 0 < ρ j) (hρ' : ∀ j, 0 < ρ' j)
    (G : Work.NN.Core.TelTwoDF.Geom n) {Cdat : Fin n → ℝ} {χ : Work.NN.Core.Cn n → ℂ}
    (hbC : ∀ j, G.b j < Cdat j) (hCρ : ∀ j, Cdat j < ρ j)
    (hχdiff : ∀ m : ℕ, ContDiff ℝ m χ) (hχcpt : HasCompactSupport χ)
    (hχts : tsupport χ ⊆ Work.CR.Flat.polydisc (0 : Work.NN.Core.Cn n) ρ)
    (hχone : ∀ z : Work.NN.Core.Cn n, (∀ j, ‖z j‖ < Cdat j) → χ z = 1)
    (hρ'e : ∀ j, ρ' j < G.e j)
    {η : Fin n → Fin n → Work.NN.Core.Cn n → ℂ}
    (hη : ∀ i l, AnalyticOn ℝ (η i l) (Work.CR.Flat.polydisc 0 ρ)) :
    ∀ j : Fin n, AnalyticOn ℝ (Work.NN.Core.TelTwoDF.TtwoDF G χ η j)
      (Work.CR.Flat.polydisc 0 ρ') := by
  have hρopen : IsOpen (Work.CR.Flat.polydisc (0 : Cn n) ρ) := Work.CR.Flat.isOpen_polydisc _ _
  -- ## The cut-off data are globally smooth
  have hetaSm : ∀ i l, ContDiff ℝ 1 (chiMul χ η i l) := by
    intro i l
    have hOn0 : ContDiffOn ℝ (⊤ : ℕ∞ω) (η i l) (Work.CR.Flat.polydisc (0 : Cn n) ρ) :=
      (hη i l).contDiffOn hρopen.uniqueDiffOn
    have hOn : ContDiffOn ℝ 1 (η i l) (Work.CR.Flat.polydisc (0 : Cn n) ρ) := hOn0.of_le le_top
    exact contDiff_mul_of_contDiffOn_of_tsupport_subset hρopen (hχdiff 1) hχts hOn
  -- ## The base case of the induction
  have hbase : ∀ i l, AnalyticOn ℝ (chiMul χ η i l)
      (Work.CR.Flat.polydisc 0 (rad G Cdat ρ' 0)) := by
    intro i l
    refine AnalyticOn.congr ((hη i l).mono ?_) ?_
    · refine Work.CR.Flat.polydisc_mono (fun k => ?_)
      have h1 := rad_zero_lt_Cdat (G := G) (Cdat := Cdat) (ρ' := ρ') hbC k
      have h2 := hCρ k
      linarith
    · intro z hz
      rw [chiMul_apply]
      have hzC : ∀ j, ‖z j‖ < Cdat j := by
        intro j
        have h1 := rad_zero_lt_Cdat (G := G) (Cdat := Cdat) (ρ' := ρ') hbC j
        have h2 : ‖z j‖ < rad G Cdat ρ' 0 j := by simpa using hz j
        linarith
      rw [hχone z hzC, one_mul]
  -- ## The induction over the stages
  have hind : ∀ m, m ≤ n → ∀ i l, AnalyticOn ℝ (uD G (chiMul χ η) m i l)
      (Work.CR.Flat.polydisc 0 (rad G Cdat ρ' m)) := by
    intro m
    induction m with
    | zero => intro _; simpa using hbase
    | succ m ih =>
      intro hm i l
      have hm' : m < n := by omega
      have hmle : m ≤ n := le_of_lt hm'
      rw [uD_succ_of_lt G (chiMul χ η) hm']
      set s : Fin n := ⟨m, hm'⟩ with hsdef
      have hEq : Set.EqOn (uStep G s (uD G (chiMul χ η) m) i l)
          (fun z => if i = s ∨ l = s then 0
            else TL G s (fun y => kappabar G s y * uD G (chiMul χ η) m i l y) z)
          (Work.CR.Flat.polydisc 0 (rad G Cdat ρ' (m + 1))) := by
        intro z hz
        rw [uStep_apply]
        have hzs : ‖z s‖ < rad G Cdat ρ' (m + 1) s := by simpa using hz s
        have hlt : rad G Cdat ρ' (m + 1) s < G.a s := by
          have h := rad_lt_a (G := G) (Cdat := Cdat) (ρ' := ρ') s hρ'e
          simpa [hsdef] using h
        have hκ : kappa G s z = 1 := kappa_eq_one G s (le_of_lt (lt_trans hzs hlt))
        rw [hκ]
        simp
      refine AnalyticOn.congr ?_ hEq
      by_cases hc : i = s ∨ l = s
      · rw [show (fun z : Cn n => if i = s ∨ l = s then (0 : ℂ)
            else TL G s (fun y => kappabar G s y * uD G (chiMul χ η) m i l y) z)
            = fun _ => (0 : ℂ) from by
          funext z; rw [if_pos hc]]
        exact analyticOn_const
      · rw [show (fun z : Cn n => if i = s ∨ l = s then (0 : ℂ)
            else TL G s (fun y => kappabar G s y * uD G (chiMul χ η) m i l y) z)
            = fun z => TL G s (fun y => kappabar G s y * uD G (chiMul χ η) m i l y) z from by
          funext z; rw [if_neg hc]]
        have hcont : Continuous
            (fun y : Cn n => kappabar G s y * uD G (chiMul χ η) m i l y) :=
          (((contDiff_kappabar G s).of_le (le_infty'' 1)).mul
            (uD_contDiff_k G hetaSm m hmle i l)).continuous
        rw [show (fun z : Cn n => TL G s
              (fun y => kappabar G s y * uD G (chiMul χ η) m i l y) z)
            = fun z => Work.CR.Flat.Cauchy.dbarTransform (G.r s) s
                (fun y => kappabar G s y * uD G (chiMul χ η) m i l y) z from by
          funext z; rw [TL_eq G s hcont]]
        refine analyticOn_dbarTransform_dbarC_sharpCut_mul (s := s) (a := G.a s) (b := G.b s) (r := G.r s)
          (G.ha s) (G.hab s) (G.hbr s) (Q := rad G Cdat ρ' m) (ρ' := rad G Cdat ρ' (m + 1))
          (fun k => rad_pos hbC hρ' hρ'e hmle k) ?_ ?_ ?_ ?_ ?_
        · rw [show rad G Cdat ρ' m s = G.b s + (Cdat s - G.b s) * gp m from rad_self s]
          have h1 : 0 < (Cdat s - G.b s) * gp m :=
            mul_pos (by have := hbC s; linarith) (gp_pos m)
          linarith
        · have h := rad_lt_a (G := G) (Cdat := Cdat) (ρ' := ρ') s hρ'e
          simpa [hsdef] using h
        · intro k hk
          have h := rad_mono (G := G) (Cdat := Cdat) (ρ' := ρ') hbC hρ'e m k
          simpa [hsdef] using h
        · exact ih hmle i l
        · exact (uD_contDiff_k G hetaSm m hmle i l).continuous
  -- ## The final output
  intro j
  rw [TtwoDF_apply]
  show AnalyticOn ℝ (S2 G (chiMul χ η) j) (Work.CR.Flat.polydisc 0 ρ')
  rw [show S2 G (chiMul χ η) j = ∑ s : Fin n, uPsi G (chiMul χ η) s j from by
    funext z; rw [S2_apply, Finset.sum_apply]]
  refine Finset.sum_induction (fun s : Fin n => uPsi G (chiMul χ η) s j)
    (fun g => AnalyticOn ℝ g (Work.CR.Flat.polydisc 0 ρ'))
    (fun f g hf hg => hf.add hg) (analyticOn_const) (fun s _ => ?_)
  have hs : (s : ℕ) ≤ n := le_of_lt s.isLt
  have hcont : Continuous
      (fun y : Cn n => kappa G s y * uD G (chiMul χ η) (s : ℕ) s j y) :=
    (((contDiff_kappa G s).of_le (le_infty'' 1)).mul
      (uD_contDiff_k G hetaSm (s : ℕ) hs s j)).continuous
  rw [show uPsi G (chiMul χ η) s j
      = fun z => Work.CR.Flat.Cauchy.dbarTransform (G.r s) s
          (fun y => kappa G s y * uD G (chiMul χ η) (s : ℕ) s j y) z from by
    funext z; rw [uPsi_apply, TL_eq G s hcont]]
  refine analyticOn_dbarTransform_sharpCut_mul (s := s) (a := G.a s) (b := G.b s) (r := G.r s)
    (G.ha s) (G.hab s) (G.hbr s) (Q := rad G Cdat ρ' (s : ℕ)) (ρ' := ρ')
    (fun k => rad_pos hbC hρ' hρ'e hs k) ?_ ?_ ?_ ?_ ?_
  · rw [show rad G Cdat ρ' (s : ℕ) s = G.b s + (Cdat s - G.b s) * gp (s : ℕ) from rad_self s]
    have h1 : 0 < (Cdat s - G.b s) * gp (s : ℕ) :=
      mul_pos (by have := hbC s; linarith) (gp_pos _)
    linarith
  · have h1 := hρ'e s
    have h2 := G.hea s
    linarith
  · intro k hk
    exact rho_lt_rad hbC hρ'e hs k
  · exact hind (s : ℕ) hs s j
  · exact (uD_contDiff_k G hetaSm (s : ℕ) hs s j).continuous

end Work.NN.Core.TelTwoDF
