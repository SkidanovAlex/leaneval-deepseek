import Mathlib
import Submission.Work.BourgainPlan.Maximal.mst_scalar_defs
import Submission.Work.BourgainPlan.Maximal.l2_defs
import Submission.Work.BourgainPlan.Maximal.major_arc_model

/-!
# The MST §4 – §5 vocabulary: the complete-sum weight `G`, the model symbols `ν_n`, `ν_n^s`

Mirek–Stein–Trojan §4.2 (`REFS/MirekSteinTrojan_1512.07518_maximal.tex`) introduce, for each level
`n` and each `s < n`,

    ν_{2^n}(ξ)   = Σ_{a/q ∈ 𝒰(n)}            G(a/q) Φ_{2^n}(ξ - a/q) η_n(ξ - a/q),
    ν_{2^n}^s(ξ) = Σ_{a/q ∈ 𝒰(s+1)∖𝒰(s)}    G(a/q) Φ_{2^n}(ξ - a/q) η_s(ξ - a/q),

with `𝒰(n) = mstU l n` the Ionescu–Wainger superset of level `n`, `η_n = mstEta d χ η n` the level
bump, `Φ_N = mstProf P N` the profile, and `G(a/q) = q⁻¹ Σ_{r<q} e(a P(r)/q) = polyWeight P q a`
the complete (Gauss) sum.

The arcs `𝒰(n)` are *points of the circle*, so a weight on them must be a function of the point;
the natural choice is the complete sum of the *canonical* representative of the point, and this is
what `mstG` encodes: for a circle point `β` with a representative `β = arcPt q a` and
`0 ≤ a < q`, `0 < q`, it returns `polyWeight P q a`.  Well-definedness needs
`polyWeight_arcPt_congr`: for representatives with `0 ≤ a < q` and `0 ≤ a' < q'` the values agree
whenever `arcPt q a = arcPt q' a'` (the two rationals `a/q`, `a'/q'` in `[0,1)` then coincide, and
`polyWeight` is invariant under passing to a common multiple).  The facts about `mstG` that the
estimates use — its value on a given representative (`mstG_spec`) and the Weyl/Gauss decay
(`mstG_gauss`) — are proved in the companion module `mstG_spec`.
-/

open MeasureTheory Finset
open scoped BigOperators ENNReal

set_option autoImplicit false

namespace Work.BourgainPlan.Maximal

open Work.BourgainPlan.IonescuWainger

noncomputable section

local notation "haarT" => (AddCircle.haarAddCircle (T := 1))

/-! ## The complete-sum weight -/

/-- **The complete (Gauss) sum attached to a circle point**: if the point `β` has a representative
`β = arcPt q a` with `0 < q`, `0 ≤ a < q`, this is `polyWeight P q a = q⁻¹ Σ_{r<q} e(a P(r)/q)`;
otherwise `0`.  (`polyWeight_arcPt_congr` shows the value does not depend on the representative
within that class, so this is well defined; `mstG_spec` computes it.) -/
noncomputable def mstG (P : Polynomial ℤ)
    (β : Work.BourgainPlan.IonescuWainger.Circle) : ℂ := by
  classical
  exact
    if h : ∃ (q : ℕ) (a : ℤ), 0 < q ∧ 0 ≤ a ∧ a < q ∧
        Work.BourgainPlan.IonescuWainger.arcPt q a = β
      then polyWeight P (Classical.choose h) (Classical.choose (Classical.choose_spec h))
      else 0

/-- `‖mstG P β‖ ≤ 1`: the value of `mstG` is either `0` or a complete sum `polyWeight P q a`, an
average of `q` unit complex numbers. -/
theorem mstG_norm_le_one (P : Polynomial ℤ)
    (β : Work.BourgainPlan.IonescuWainger.Circle) : ‖mstG P β‖ ≤ 1 := by
  classical
  unfold mstG
  split
  · next h => exact norm_polyWeight_le_one P _ _
  · simp

/-! ## The model symbols `ν_n` and `ν_n^s`

**Sign convention (important).**  The `L^∞(𝕋)`-class of the density average `discAvgZC P N` has the
a.e. value `star (mstWeyl P N ξ)` (`khatZMult_coeFn_star_mstWeyl`), i.e. the *conjugate* of the Weyl
kernel `N⁻¹ Σ_{n<N} e(ξ P(n))` that `major_arc_nbd_bound` compares with `polyWeight · polyProfile`.
Consequently the major-arc model that is close to `m_{2^n} Ξ_n` — where `Ξ_n` is the projection
symbol — is the *conjugate* model `Σ_{β ∈ 𝒰(n)} star (G(β) Φ_{2^n}(ξ−β)) η_n(ξ−β)`, not MST's
`Σ_β G(β) Φ_{2^n}(ξ−β) η_n(ξ−β)` itself.  (`star (a * b) = star a * star b`, so this is
`mstModelFn (star ∘ mstG P) (star ∘ mstProf P (2^n)) (mstEta …) …`.)  The *moduli* are of course
unchanged, so every estimate of §4–§5 — all of which are bounds on moduli — is unaffected.

**Level-index convention.**  MST's level sets satisfy `𝒰_0 = ∅` (their `Σ_{⊆A}` is empty for the
trivial group), so the annuli `𝒰((s+1)^l) ∖ 𝒰(s^l)`, `s ≥ 0`, tile all of `𝒰(n^l)`: for `s = 0` the
annulus is `𝒰_{1^l} ∖ ∅`, which contains the trivial point `0` and carries the level-`0` bump `η_0`.
With Tao's supersets the convention `𝒰(0) = mstU l 0 = {0}` fails to give this (`0` would then be
left over, and the leftover term `Φ_{2^n}(ξ) η_n(ξ)` is *not* small at `ξ = 0`), so `mstLevel`
below restores `∅` at level `0`.  Then `Σ_{0 ≤ s < n} ν_{2^n}^s` indeed equals `ν_{2^n}` up to the
error of §4.2 eq. (76). -/

/-- The MST level set with the convention `𝒰(0) := ∅` (see the discussion above). -/
def mstLevel (l s : ℕ) : Finset Work.BourgainPlan.IonescuWainger.Circle :=
  if s = 0 then ∅ else mstU l s

@[simp] theorem mstLevel_zero (l : ℕ) : mstLevel l 0 = ∅ := by simp [mstLevel]

theorem mstLevel_succ (l s : ℕ) : mstLevel l (s + 1) = mstU l (s + 1) := by
  simp [mstLevel]

/-- **MST's `ν_{2^n}`** (with the conjugation of the sign convention above): the major-arc model
symbol at level `n`, `Σ_{β ∈ 𝒰(n)} star (G(β) Φ_{2^n}(ξ - β)) η_n(ξ - β)`. -/
def mstNu (P : Polynomial ℤ) (l d : ℕ) (χ : ℝ) (η : ℝ → ℂ) (n : ℕ) :
    Work.BourgainPlan.IonescuWainger.Circle → ℂ :=
  mstModelFn (fun β => star (mstG P β))
    (fun ζ => star (mstProf P (2 ^ n) ζ)) (mstEta d χ η n) (mstU l n)

/-- **MST's `ν_{2^n}^s`**: the level-`s` piece of the major-arc model,
`Σ_{β ∈ 𝒰(s+1)∖𝒰(s)} star (G(β) Φ_{2^n}(ξ - β)) η_s(ξ - β)` (the bump is the level-`s` bump `η_s`,
the profile is the level-`n` profile `Φ_{2^n}`), with the `𝒰(0) := ∅` convention `mstLevel`. -/
def mstNuS (P : Polynomial ℤ) (l d : ℕ) (χ : ℝ) (η : ℝ → ℂ) (n s : ℕ) :
    Work.BourgainPlan.IonescuWainger.Circle → ℂ :=
  mstModelFn (fun β => star (mstG P β))
    (fun ζ => star (mstProf P (2 ^ n) ζ)) (mstEta d χ η s) (mstLevel l (s + 1) \ mstLevel l s)

@[simp] theorem mstNu_apply (P : Polynomial ℤ) (l d : ℕ) (χ : ℝ) (η : ℝ → ℂ) (n : ℕ)
    (ξ : Work.BourgainPlan.IonescuWainger.Circle) :
    mstNu P l d χ η n ξ
      = ∑ β ∈ mstU l n,
          star (mstG P β) * (star (mstProf P (2 ^ n) (ξ - β)) * mstEta d χ η n (ξ - β)) := by
  simp only [mstNu, mstModelFn_apply]

@[simp] theorem mstNuS_apply (P : Polynomial ℤ) (l d : ℕ) (χ : ℝ) (η : ℝ → ℂ) (n s : ℕ)
    (ξ : Work.BourgainPlan.IonescuWainger.Circle) :
    mstNuS P l d χ η n s ξ
      = ∑ β ∈ mstLevel l (s + 1) \ mstLevel l s,
          star (mstG P β) * (star (mstProf P (2 ^ n) (ξ - β)) * mstEta d χ η s (ξ - β)) := by
  simp only [mstNuS, mstModelFn_apply]

/-- The MST threshold `κ_s = 20 d (⌊(s+1)^{1/10}⌋ + 1)` separating the small scales `k ≤ 2^{κ_s}`
(from the Rademacher–Menshov/Plancherel argument) from the large scales `k ≥ 2^{κ_s}` (from the
`Q_s`-periodic freezing and the sampling principle) in the level estimates of §4.3–4.4. -/
def mstKappa (P : Polynomial ℤ) (s : ℕ) : ℕ :=
  20 * P.natDegree * (⌊((s : ℝ) + 1) ^ (1 / 10 : ℝ)⌋₊ + 1)

/-- The `L^∞(𝕋)`-class of the level-`s` piece `ν_{2^n}^s` of the major-arc model. -/
def mstNuSCls (P : Polynomial ℤ) (l d : ℕ) (χ : ℝ) (η : ℝ → ℂ) (n s : ℕ)
    (h : MemLp (mstNuS P l d χ η n s) ⊤ haarT) : Lp ℂ ⊤ haarT :=
  h.toLp (mstNuS P l d χ η n s)

/-- The a.e. value of `mstNuSCls`. -/
theorem mstNuSCls_coeFn (P : Polynomial ℤ) (l d : ℕ) (χ : ℝ) (η : ℝ → ℂ) (n s : ℕ)
    (h : MemLp (mstNuS P l d χ η n s) ⊤ haarT) :
    (mstNuSCls P l d χ η n s h : Work.BourgainPlan.IonescuWainger.Circle → ℂ)
      =ᵐ[haarT] mstNuS P l d χ η n s :=
  MemLp.coeFn_toLp _

/-! ## The multiplier classes of the two major-arc errors

With the three symbols `mstNu`, `mstNuS` and the projection symbol `Ξ_n` in hand, MST §4.2 compares

* `m_{2^n} Ξ_n` with `ν_{2^n}`      (eqs. (70), (72), (73)), and
* `ν_{2^n}` with `Σ_{0 ≤ s < n} ν_{2^n}^s`  (eqs. (76), (78), (80)).

Both are differences of multipliers; the two error estimates are stated in the companion modules
`mst_major_err1` and `mst_major_err2`. -/

/-- The `L^∞(𝕋)`-class of the projection symbol `m_{2^n} Ξ_n`. -/
def mstProjCls (P : Polynomial ℤ) (l d : ℕ) (χ : ℝ) (η : ℝ → ℂ) (n : ℕ)
    (hη : MemLp (mstEta d χ η n) ⊤ haarT) : Lp ℂ ⊤ haarT :=
  khatZMult P (2 ^ n) • arcSymbolLp (mstEta d χ η n) hη (mstU l n)

/-- The `L^∞(𝕋)`-class of the model symbol `ν_{2^n}`. -/
def mstNuCls (P : Polynomial ℤ) (l d : ℕ) (χ : ℝ) (η : ℝ → ℂ) (n : ℕ)
    (h : MemLp (mstNu P l d χ η n) ⊤ haarT) : Lp ℂ ⊤ haarT :=
  h.toLp (mstNu P l d χ η n)

/-- The `L^∞(𝕋)`-class of the model symbol `Σ_{0 ≤ s < n} ν_{2^n}^s`. -/
def mstNuSumCls (P : Polynomial ℤ) (l d : ℕ) (χ : ℝ) (η : ℝ → ℂ) (n : ℕ)
    (h : ∀ s : ℕ, MemLp (mstNuS P l d χ η n s) ⊤ haarT) : Lp ℂ ⊤ haarT :=
  ∑ s ∈ Finset.range n, (h s).toLp (mstNuS P l d χ η n s)

/-- **The first major-arc error multiplier class** `m_{2^n} Ξ_n - ν_{2^n}`. -/
def mstMajErr1Cls (P : Polynomial ℤ) (l d : ℕ) (χ : ℝ) (η : ℝ → ℂ) (n : ℕ)
    (hη : MemLp (mstEta d χ η n) ⊤ haarT)
    (hν : MemLp (mstNu P l d χ η n) ⊤ haarT) : Lp ℂ ⊤ haarT :=
  mstProjCls P l d χ η n hη - mstNuCls P l d χ η n hν

/-- **The second major-arc error multiplier class** `ν_{2^n} - Σ_{0 ≤ s < n} ν_{2^n}^s`. -/
def mstMajErr2Cls (P : Polynomial ℤ) (l d : ℕ) (χ : ℝ) (η : ℝ → ℂ) (n : ℕ)
    (hν : MemLp (mstNu P l d χ η n) ⊤ haarT)
    (h : ∀ s : ℕ, MemLp (mstNuS P l d χ η n s) ⊤ haarT) : Lp ℂ ⊤ haarT :=
  mstNuCls P l d χ η n hν - mstNuSumCls P l d χ η n h

end

end Work.BourgainPlan.Maximal
