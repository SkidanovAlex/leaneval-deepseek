import Mathlib
import Mathlib.Analysis.Complex.CoveringMap
import Mathlib.Analysis.SpecialFunctions.Complex.Log

/-!
# The winding homomorphism extracted from the monodromy of the log cover

Let `Y` be a topological space, `ℓ : Y → ℂ` continuous with `ℓ y ≠ 0` everywhere, and

  `logSpace ℓ := {p : Y × ℂ // Complex.exp p.2 = ℓ p.1}`

its logarithmic étale space, with projection `logProj ℓ`.  If `logProj ℓ` is a covering map
(`Work.SimplyConnected.ABS.isCoveringMap_logSpace`, reviewed, in flight), the monodromy of this
covering around a loop `γ` at `y₀` moves the lift `(y₀, w₀)` of `ℓ y₀` to another point of the same
fibre, whose `ℂ`-coordinate differs from `w₀` by a *unique* integer multiple of `2πi`:

  `monodromy γ (y₀,w₀) = (y₀, w₀ + W γ · 2πi)`,  `W γ ∈ ℤ`,

and `W : π₁(Y,y₀) →+ ℤ` is additive.  For `Y = X ∖ {x₀}` and `ℓ` the normalized chart coordinate
near `x₀` this is the winding number about the puncture, i.e. the integer-valued period
homomorphism consumed by `Work.SimplyConnected.ABS.unitGreen_modulus_of_integerValuedPeriods`.

## Status

* `monodromy_logSpace_eq_shift` — **proved, sorry-free** (the extraction of the integer for one
  loop, as a unique-existence statement).
* `exists_windingHom` — the assembly into an additive homomorphism; stated with its plan, the
  remaining obligation of this file.  Additivity: `IsCoveringMap.monodromy_trans_apply` composes
  monodromies, and `monodromy` commutes with the deck shift `w ↦ w + 2πi` (same argument as
  `Submission.monodromy_conjFiberShift`, via `Submission.monodromy_mk_liftPath`), so the shift
  `2πi·W` is additive, and the integers are additive by uniqueness.
-/

open Topology

namespace Work.SimplyConnected.ABS

/-- The logarithmic étale space of `ℓ : Y → ℂ`: the pairs `(y, w)` with `exp w = ℓ y`. -/
def logSpace {Y : Type*} (ℓ : Y → ℂ) : Set (Y × ℂ) := {p | Complex.exp p.2 = ℓ p.1}

/-- The projection of the logarithmic étale space. -/
def logProj {Y : Type*} (ℓ : Y → ℂ) : {p : Y × ℂ // Complex.exp p.2 = ℓ p.1} → Y :=
  fun q => (q : Y × ℂ).1

/-- The `ℂ`-coordinate of a point of the logarithmic étale space. -/
def logCoord {Y : Type*} (ℓ : Y → ℂ) (p : {p : Y × ℂ // Complex.exp p.2 = ℓ p.1}) : ℂ :=
  (p : Y × ℂ).2

variable {Y : Type*} [TopologicalSpace Y] [ConnectedSpace Y]

/-- The lift `(y₀, w₀)` of `ℓ y₀`, as a point of the fibre of the log cover over `y₀`. -/
def logPt (ℓ : Y → ℂ) (y₀ : Y) (w₀ : ℂ) (hw₀ : Complex.exp w₀ = ℓ y₀) :
    ↥(logProj ℓ ⁻¹' {y₀}) :=
  ⟨⟨(y₀, w₀), hw₀⟩, by simp [logProj]⟩

/-! ## The deck shift `w ↦ w + n·2πi`

The shift `w ↦ w + c` preserves the logarithmic étale space exactly for `c ∈ 2πiℤ` — unlike the
conjugate shift of `Submission/Conjugate.lean`, which is an `ℝ`-translation because the conjugate
fibre is a *horizontal* condition.  Hence the shift here is indexed by `n : ℤ`.
-/

/-- The deck shift `w ↦ w + n · 2πi` on the logarithmic étale space. -/
noncomputable def logShift (ℓ : Y → ℂ) (n : ℤ) :
    {p : Y × ℂ // Complex.exp p.2 = ℓ p.1} → {p : Y × ℂ // Complex.exp p.2 = ℓ p.1} :=
  fun q => ⟨((q : Y × ℂ).1, (q : Y × ℂ).2 + (n : ℂ) * (2 * Real.pi * Complex.I)), by
    rw [Complex.exp_add, Complex.exp_eq_one_iff.mpr ⟨n, rfl⟩, mul_one]
    exact q.2⟩

@[simp] theorem logShift_coe (ℓ : Y → ℂ) (n : ℤ)
    (q : {p : Y × ℂ // Complex.exp p.2 = ℓ p.1}) :
    ((logShift ℓ n q : {p : Y × ℂ // Complex.exp p.2 = ℓ p.1}) : Y × ℂ)
      = ((q : Y × ℂ).1, (q : Y × ℂ).2 + (n : ℂ) * (2 * Real.pi * Complex.I)) := rfl

/-- The deck shift does not move the point of `Y`. -/
theorem logProj_logShift (ℓ : Y → ℂ) (n : ℤ)
    (q : {p : Y × ℂ // Complex.exp p.2 = ℓ p.1}) :
    logProj ℓ (logShift ℓ n q) = logProj ℓ q := rfl

/-- The deck shifts add. -/
theorem logShift_add (ℓ : Y → ℂ) (n m : ℤ)
    (q : {p : Y × ℂ // Complex.exp p.2 = ℓ p.1}) :
    logShift ℓ n (logShift ℓ m q) = logShift ℓ (n + m) q := by
  apply Subtype.ext
  apply Prod.ext
  · simp only [logShift_coe]
  · show (q : Y × ℂ).2 + (m : ℂ) * (2 * Real.pi * Complex.I)
        + (n : ℂ) * (2 * Real.pi * Complex.I)
      = (q : Y × ℂ).2 + ((n + m : ℤ) : ℂ) * (2 * Real.pi * Complex.I)
    push_cast
    ring

/-- The fibre condition after the deck shift: the point of `Y` is unchanged. -/
theorem logFiberShift_mem (ℓ : Y → ℂ) (n : ℤ) {y : Y} (e : ↥(logProj ℓ ⁻¹' {y})) :
    ((logShift ℓ n (e : {p : Y × ℂ // Complex.exp p.2 = ℓ p.1}) :
      {p : Y × ℂ // Complex.exp p.2 = ℓ p.1}) : Y × ℂ).1 = y := by
  rw [logShift_coe]
  exact e.2

/-- The deck shift restricted to a fibre of the log cover. -/
noncomputable def logFiberShift (ℓ : Y → ℂ) (n : ℤ) {y : Y} (e : ↥(logProj ℓ ⁻¹' {y})) :
    ↥(logProj ℓ ⁻¹' {y}) :=
  ⟨logShift ℓ n (e : {p : Y × ℂ // Complex.exp p.2 = ℓ p.1}), logFiberShift_mem ℓ n e⟩

@[simp] theorem logFiberShift_coe (ℓ : Y → ℂ) (n : ℤ) {y : Y}
    (e : ↥(logProj ℓ ⁻¹' {y})) :
    (logFiberShift ℓ n e).1
      = logShift ℓ n (e : {p : Y × ℂ // Complex.exp p.2 = ℓ p.1}) := rfl

/-- The deck shift is continuous. -/
theorem continuous_logShift (ℓ : Y → ℂ) (n : ℤ) : Continuous (logShift ℓ n) := by
  -- `logShift ℓ n` is *definitionally* the subtype map of the continuous `q ↦ (q.1, q.2 + n·2πi)`,
  -- so `Continuous.subtype_mk` leaves only the continuity of that map; the fibre condition is
  -- discharged by the definition itself.
  refine Continuous.subtype_mk ?_ ?_
  · exact (continuous_fst.comp continuous_subtype_val).prodMk
      ((continuous_snd.comp continuous_subtype_val).add continuous_const)

/-- The monodromy of a covering, read off from the lift of a path.  (This is
`Submission.monodromy_mk_liftPath`; it is proved by `rfl` and is kept local to avoid importing the
whole `Submission.Conjugate` chapter.) -/
theorem monodromy_mk_liftPath {E : Type*} [TopologicalSpace E] {p : E → Y}
    (cov : IsCoveringMap p) {a b : Y} (γ : Path a b) (e : E) (he : p e = a) :
    (cov.monodromy (Path.Homotopic.Quotient.mk γ) ⟨e, he⟩).1 =
      cov.liftPath γ e (γ.source.trans he.symm) 1 := rfl

/-- Lifting commutes with the deck shift (transcription of
`Submission.liftPath_conjShift_apply`). -/
theorem liftPath_logShift_apply (ℓ : Y → ℂ) (hcov : IsCoveringMap (logProj ℓ)) (n : ℤ)
    {y y' : Y} (γ : Path y y') (e : {p : Y × ℂ // Complex.exp p.2 = ℓ p.1})
    (he : logProj ℓ e = y) :
    ∀ t : unitInterval,
      hcov.liftPath γ (logShift ℓ n e)
          (γ.source.trans ((logProj_logShift ℓ n e).trans he).symm) t
        = logShift ℓ n (hcov.liftPath γ e (γ.source.trans he.symm) t) := by
  have hσ : Continuous (logShift ℓ n) := continuous_logShift ℓ n
  intro t
  have h := (hcov.eq_liftPath_iff' (γ := γ) (e := logShift ℓ n e)
    (γ_0 := γ.source.trans ((logProj_logShift ℓ n e).trans he).symm)
    (Γ := ⟨fun s => logShift ℓ n (hcov.liftPath γ e (γ.source.trans he.symm) s),
      hσ.comp (hcov.liftPath γ e (γ.source.trans he.symm)).continuous⟩)).mpr ?_
  · rw [← h]
    rfl
  · refine ⟨?_, ?_⟩
    · funext s
      simp only [ContinuousMap.coe_mk, Function.comp_apply]
      rw [logProj_logShift]
      exact congr_fun (hcov.liftPath_lifts γ e (γ.source.trans he.symm)) s
    · simp only [ContinuousMap.coe_mk]
      rw [hcov.liftPath_zero]

/-- **The monodromy commutes with the deck shift** (transcription of
`Submission.monodromy_conjFiberShift`). -/
theorem monodromy_logShift (ℓ : Y → ℂ) (hcov : IsCoveringMap (logProj ℓ)) (n : ℤ)
    {y y' : Y} (γ : Path.Homotopic.Quotient y y') (e : ↥(logProj ℓ ⁻¹' {y})) :
    hcov.monodromy γ (logFiberShift ℓ n e) = logFiberShift ℓ n (hcov.monodromy γ e) := by
  obtain ⟨γ⟩ := γ
  apply Subtype.ext
  apply Subtype.ext
  apply Prod.ext
  · exact (hcov.monodromy _ (logFiberShift ℓ n e)).2.trans
      ((logFiberShift ℓ n (hcov.monodromy _ e)).2).symm
  · show ((hcov.monodromy (Path.Homotopic.Quotient.mk γ) (logFiberShift ℓ n e) :
        ↥(logProj ℓ ⁻¹' {y'})).1 : Y × ℂ).2
      = ((logFiberShift ℓ n (hcov.monodromy (Path.Homotopic.Quotient.mk γ) e) :
        ↥(logProj ℓ ⁻¹' {y'})).1 : Y × ℂ).2
    rw [show logFiberShift ℓ n e
        = (⟨logShift ℓ n (e : {p : Y × ℂ // Complex.exp p.2 = ℓ p.1}),
            logFiberShift_mem ℓ n e⟩ : ↥(logProj ℓ ⁻¹' {y})) from rfl]
    rw [monodromy_mk_liftPath hcov γ (logShift ℓ n (e : {p : Y × ℂ // Complex.exp p.2 = ℓ p.1}))
      (logFiberShift_mem ℓ n e)]
    rw [show logFiberShift ℓ n (hcov.monodromy (Path.Homotopic.Quotient.mk γ) e)
        = (⟨logShift ℓ n (hcov.liftPath γ (e : {p : Y × ℂ // Complex.exp p.2 = ℓ p.1})
              (γ.source.trans e.2.symm) 1),
            logFiberShift_mem ℓ n (hcov.monodromy (Path.Homotopic.Quotient.mk γ) e)⟩ :
          ↥(logProj ℓ ⁻¹' {y'})) from by
      refine Subtype.ext ?_
      exact congrArg (logShift ℓ n) (monodromy_mk_liftPath hcov γ
        (e : {p : Y × ℂ // Complex.exp p.2 = ℓ p.1}) e.2)]
    exact congrArg (fun z : {p : Y × ℂ // Complex.exp p.2 = ℓ p.1} => ((z : Y × ℂ)).2)
      (liftPath_logShift_apply ℓ hcov n γ (e : {p : Y × ℂ // Complex.exp p.2 = ℓ p.1}) e.2 1)

/-- **The integer read off the monodromy of the log cover.**  The monodromy of the covering
`logProj ℓ` around a loop `γ` at `y₀` moves the lift `(y₀, w₀)` of `ℓ y₀` to a point of the same
fibre, whose `ℂ`-coordinate is `w₀ + n · 2πi` for a **unique** `n : ℤ`. -/
theorem monodromy_logSpace_eq_shift (ℓ : Y → ℂ) (y₀ : Y) (w₀ : ℂ)
    (hw₀ : Complex.exp w₀ = ℓ y₀) (hcov : IsCoveringMap (logProj ℓ))
    (γ : FundamentalGroup Y y₀) :
    ∃! n : ℤ,
      logCoord ℓ (hcov.monodromy γ (logPt ℓ y₀ w₀ hw₀)).1
        = w₀ + (n : ℂ) * (2 * Real.pi * Complex.I) := by
  have hfib : ((hcov.monodromy γ (logPt ℓ y₀ w₀ hw₀)).1 : Y × ℂ).1 = y₀ :=
    (hcov.monodromy γ (logPt ℓ y₀ w₀ hw₀)).2
  have hcond : Complex.exp (logCoord ℓ (hcov.monodromy γ (logPt ℓ y₀ w₀ hw₀)).1) = ℓ y₀ := by
    have h := (hcov.monodromy γ (logPt ℓ y₀ w₀ hw₀)).1.2
    simpa [logCoord, hfib] using h
  have hexp : Complex.exp (logCoord ℓ (hcov.monodromy γ (logPt ℓ y₀ w₀ hw₀)).1)
      = Complex.exp w₀ := by rw [hcond, hw₀]
  obtain ⟨n, hn⟩ := Complex.exp_eq_exp_iff_exists_int.mp hexp
  have hn' : logCoord ℓ (hcov.monodromy γ (logPt ℓ y₀ w₀ hw₀)).1
      = w₀ + (n : ℂ) * (2 * Real.pi * Complex.I) := by simpa using hn
  have h2π : (2 * (Real.pi : ℂ) * Complex.I) ≠ 0 :=
    mul_ne_zero (mul_ne_zero two_ne_zero (Complex.ofReal_ne_zero.mpr Real.pi_ne_zero))
      Complex.I_ne_zero
  refine ⟨n, hn', ?_⟩
  intro m' hm'
  have heq : w₀ + (n : ℂ) * (2 * Real.pi * Complex.I)
      = w₀ + (m' : ℂ) * (2 * Real.pi * Complex.I) := hn'.symm.trans hm'
  have h3 : (n : ℂ) * (2 * Real.pi * Complex.I) = (m' : ℂ) * (2 * Real.pi * Complex.I) :=
    add_left_cancel heq
  have h4 : (n : ℂ) = (m' : ℂ) := by
    have h5 : ((n : ℂ) - (m' : ℂ)) * (2 * Real.pi * Complex.I) = 0 := by
      rw [sub_mul, h3, sub_self]
    rcases mul_eq_zero.mp h5 with h6 | h7
    · exact sub_eq_zero.mp h6
    · exact absurd h7 h2π
  exact (Int.cast_injective h4).symm

/-- The coordinate of the deck-shifted fibre point, in terms of the shift. -/
theorem logCoord_logFiberShift (ℓ : Y → ℂ) (n : ℤ) {y : Y} (e : ↥(logProj ℓ ⁻¹' {y})) :
    logCoord ℓ (logFiberShift ℓ n e).1
      = logCoord ℓ (e : {p : Y × ℂ // Complex.exp p.2 = ℓ p.1})
        + (n : ℂ) * (2 * Real.pi * Complex.I) := by
  have h := logShift_coe ℓ n (e : {p : Y × ℂ // Complex.exp p.2 = ℓ p.1})
  simpa [logCoord, logFiberShift_coe] using congrArg (fun z : Y × ℂ => z.2) h

/-- The fibre shifts add. -/
theorem logFiberShift_add (ℓ : Y → ℂ) (n m : ℤ) {y : Y} (e : ↥(logProj ℓ ⁻¹' {y})) :
    logFiberShift ℓ n (logFiberShift ℓ m e) = logFiberShift ℓ (n + m) e := by
  apply Subtype.ext
  rw [logFiberShift_coe, logFiberShift_coe, logFiberShift_coe]
  exact logShift_add ℓ n m (e : {p : Y × ℂ // Complex.exp p.2 = ℓ p.1})

/-- **The winding integer of the identity loop is zero.**

This is the ingredient of `map_zero'` for the winding homomorphism: any integer witnessing
`monodromy_logSpace_eq_shift` at `γ = 1` must vanish.  The proof is that the monodromy of the
identity is the identity (`IsCoveringMap.monodromy_refl`), whose coordinate is `w₀`, so
`w₀ + n·2πi = w₀`; then `2πi ≠ 0` and injectivity of `ℤ → ℂ` give `n = 0`. -/
theorem winding_eq_zero_of_monodromy_one (ℓ : Y → ℂ) (y₀ : Y) (w₀ : ℂ)
    (hw₀ : Complex.exp w₀ = ℓ y₀) (hcov : IsCoveringMap (logProj ℓ)) (n : ℤ)
    (h : logCoord ℓ (hcov.monodromy (Path.Homotopic.Quotient.refl y₀)
          (logPt ℓ y₀ w₀ hw₀)).1
        = w₀ + (n : ℂ) * (2 * Real.pi * Complex.I)) : n = 0 := by
  have hmono : hcov.monodromy (Path.Homotopic.Quotient.refl y₀) (logPt ℓ y₀ w₀ hw₀)
      = logPt ℓ y₀ w₀ hw₀ :=
    congrFun hcov.monodromy_refl (logPt ℓ y₀ w₀ hw₀)
  have hbase : logCoord ℓ (logPt ℓ y₀ w₀ hw₀).1 = w₀ := rfl
  have hw : w₀ + (n : ℂ) * (2 * Real.pi * Complex.I) = w₀ := by
    rw [← h, congrArg (fun e => logCoord ℓ e.1) hmono]
    exact hbase
  have hzero : (n : ℂ) * (2 * Real.pi * Complex.I) = 0 :=
    add_left_cancel (hw.trans (add_zero w₀).symm)
  have h2π : (2 * (Real.pi : ℂ) * Complex.I) ≠ 0 :=
    mul_ne_zero (mul_ne_zero two_ne_zero (Complex.ofReal_ne_zero.mpr Real.pi_ne_zero))
      Complex.I_ne_zero
  have hn : (n : ℂ) = 0 := by
    rcases mul_eq_zero.mp hzero with h1 | h2
    · exact h1
    · exact absurd h2 h2π
  exact_mod_cast hn

/-- **Additivity of the winding integers** — the `map_add'` ingredient for the winding
homomorphism.  If `n`, `m`, `k` witness the monodromy equation (`monodromy_logSpace_eq_shift`)
for `γ₁`, `γ₂` and `γ₁ * γ₂` respectively, then `k = n + m`.

Proof (the shape of `Submission.conjPeriod_add`): a witness `t` for `γ` says exactly
`monodromy γ e₀ = logFiberShift t e₀`; `monodromy_trans_apply` composes the monodromies of
`γ₂` then `γ₁`, `monodromy_logShift` moves the shift out, `logFiberShift_add` adds the indices, and
`h₁₂` is compared with the result. -/
theorem winding_add_of_monodromy_mul (ℓ : Y → ℂ) (y₀ : Y) (w₀ : ℂ)
    (hw₀ : Complex.exp w₀ = ℓ y₀) (hcov : IsCoveringMap (logProj ℓ))
    (γ₁ γ₂ : FundamentalGroup Y y₀) (n m k : ℤ)
    (h₁ : logCoord ℓ (hcov.monodromy γ₁ (logPt ℓ y₀ w₀ hw₀)).1
        = w₀ + (n : ℂ) * (2 * Real.pi * Complex.I))
    (h₂ : logCoord ℓ (hcov.monodromy γ₂ (logPt ℓ y₀ w₀ hw₀)).1
        = w₀ + (m : ℂ) * (2 * Real.pi * Complex.I))
    (h₁₂ : logCoord ℓ (hcov.monodromy (γ₁ * γ₂) (logPt ℓ y₀ w₀ hw₀)).1
        = w₀ + (k : ℂ) * (2 * Real.pi * Complex.I)) : k = n + m := by
  have hpt : logCoord ℓ (logPt ℓ y₀ w₀ hw₀).1 = w₀ := rfl
  have hshift : ∀ (γ : FundamentalGroup Y y₀) (t : ℤ),
      logCoord ℓ (hcov.monodromy γ (logPt ℓ y₀ w₀ hw₀)).1
        = w₀ + (t : ℂ) * (2 * Real.pi * Complex.I) →
      hcov.monodromy γ (logPt ℓ y₀ w₀ hw₀) = logFiberShift ℓ t (logPt ℓ y₀ w₀ hw₀) := by
    intro γ t ht
    apply Subtype.ext
    apply Subtype.ext
    apply Prod.ext
    · exact (hcov.monodromy γ (logPt ℓ y₀ w₀ hw₀)).2.trans
        ((logFiberShift ℓ t (logPt ℓ y₀ w₀ hw₀)).2).symm
    · show logCoord ℓ (hcov.monodromy γ (logPt ℓ y₀ w₀ hw₀)).1
          = logCoord ℓ (logFiberShift ℓ t (logPt ℓ y₀ w₀ hw₀)).1
      rw [ht, logCoord_logFiberShift, hpt]
  have hcomp : hcov.monodromy (γ₁ * γ₂) (logPt ℓ y₀ w₀ hw₀)
      = logFiberShift ℓ (n + m) (logPt ℓ y₀ w₀ hw₀) := by
    rw [FundamentalGroup.mul_def, hcov.monodromy_trans_apply γ₂ γ₁ (logPt ℓ y₀ w₀ hw₀)]
    rw [hshift γ₂ m h₂,
      monodromy_logShift ℓ hcov m γ₁ (logPt ℓ y₀ w₀ hw₀),
      hshift γ₁ n h₁]
    simpa [add_comm] using logFiberShift_add ℓ m n (logPt ℓ y₀ w₀ hw₀)
  have hcoord : w₀ + (k : ℂ) * (2 * Real.pi * Complex.I)
      = w₀ + ((n + m : ℤ) : ℂ) * (2 * Real.pi * Complex.I) := by
    rw [← h₁₂]
    show logCoord ℓ (hcov.monodromy (γ₁ * γ₂) (logPt ℓ y₀ w₀ hw₀)).1
        = w₀ + ((n + m : ℤ) : ℂ) * (2 * Real.pi * Complex.I)
    rw [hcomp, logCoord_logFiberShift, hpt]
  have h3 : (k : ℂ) * (2 * Real.pi * Complex.I)
      = ((n + m : ℤ) : ℂ) * (2 * Real.pi * Complex.I) :=
    add_left_cancel hcoord
  have h2π : (2 * (Real.pi : ℂ) * Complex.I) ≠ 0 :=
    mul_ne_zero (mul_ne_zero two_ne_zero (Complex.ofReal_ne_zero.mpr Real.pi_ne_zero))
      Complex.I_ne_zero
  have h4 : (k : ℂ) = ((n + m : ℤ) : ℂ) := by
    have h5 : ((k : ℂ) - ((n + m : ℤ) : ℂ)) * (2 * Real.pi * Complex.I) = 0 := by
      rw [sub_mul, h3, sub_self]
    rcases mul_eq_zero.mp h5 with h6 | h7
    · exact sub_eq_zero.mp h6
    · exact absurd h7 h2π
  exact_mod_cast h4

/-- **The winding homomorphism.**  The integers extracted by `monodromy_logSpace_eq_shift` assemble
into an additive homomorphism `W : π₁(Y,y₀) →+ ℤ` with

  `monodromy γ (y₀, w₀) = (y₀, w₀ + W γ · 2πi)`.

Additivity comes from `IsCoveringMap.monodromy_trans_apply` and the commutation of `monodromy` with
the deck shift `w ↦ w + 2πi` (same proof as `Submission.monodromy_conjFiberShift`), by uniqueness of
the integer in `monodromy_logSpace_eq_shift`. -/
theorem exists_windingHom (ℓ : Y → ℂ) (hℓ : Continuous ℓ) (hne : ∀ y, ℓ y ≠ 0)
    (y₀ : Y) (w₀ : ℂ) (hw₀ : Complex.exp w₀ = ℓ y₀) (hcov : IsCoveringMap (logProj ℓ)) :
    ∃ W : Additive (FundamentalGroup Y y₀) →+ ℤ,
      ∀ γ : FundamentalGroup Y y₀,
        logCoord ℓ (hcov.monodromy γ (logPt ℓ y₀ w₀ hw₀)).1
          = w₀ + (W (Additive.ofMul γ) : ℂ) * (2 * Real.pi * Complex.I) := by
  classical
  choose W hW using fun γ : FundamentalGroup Y y₀ =>
    (monodromy_logSpace_eq_shift ℓ y₀ w₀ hw₀ hcov γ).exists
  refine ⟨{ toFun := fun a => W (Additive.toMul a)
            map_zero' := ?_
            map_add' := ?_ }, fun γ => hW γ⟩
  · exact winding_eq_zero_of_monodromy_one ℓ y₀ w₀ hw₀ hcov (W 1) (hW 1)
  · intro a b
    have h : Additive.toMul (a + b) = Additive.toMul a * Additive.toMul b := rfl
    rw [h]
    exact winding_add_of_monodromy_mul ℓ y₀ w₀ hw₀ hcov (Additive.toMul a) (Additive.toMul b)
      (W (Additive.toMul a)) (W (Additive.toMul b)) (W (Additive.toMul a * Additive.toMul b))
      (hW _) (hW _) (hW _)

end Work.SimplyConnected.ABS
