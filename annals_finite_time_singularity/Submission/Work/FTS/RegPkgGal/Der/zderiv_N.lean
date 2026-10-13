import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.Complex.Trigonometric
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
import Mathlib.Topology.Algebra.Module.ModuleTopology
import Submission.Work.FTS.RegPkgGal.Der.Defs
import Submission.Work.FTS.RegPkgGal.Der.jet_N
import Submission.Work.Construction.Defs

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

/-!
# `Work.FTS.RegPkgGal.Der.zderiv_N` — the `z`-derivative bound for `N`

`Work.FTS.RegPkgGal.C1Jet α S N h` bundles the two facts needed to differentiate the
constituents of the right-hand side of the fake-time equation in `z`:

* the joint `Jet` data (`Work.FTS.Regularity.Jet`: a uniform bound and a joint `α`-Hölder
  modulus on the strip `z ≥ 0`, `θ ∈ Iθ`, `τ ∈ [0,S]`), and
* the `z`-differentiability of every slice `z ↦ h z θ τ` on `z > 0` with derivative bounded
  by `N`, uniformly in `(θ,τ)`.

The target statement below (the `C1Jet` counterpart of `Der.jet_N`) says that the term

  `N αp F Φ = 2·ℛ(Φ̃)F - 2·U(Φ̃)∂_θF - 2αp·V(Φ̃)D_zF - (1/2)·sin2θ·(F,K)∂_θF - sin²θ·(F,K)F`

is a `C1Jet` whenever its seven constituents are (here `αp = pExp α = 3α`, `F = F_τ = F_* + g(τ)`
and `Φ̃ = ΦTil αp F Φ`).

## The contents of this file

Six closure lemmas for `C1Jet` (nothing else is needed — `N` is a sum of products of the
seven inputs, each scaled by a constant):

* `C1Jet.neg`, `C1Jet.add`, `C1Jet.mul`, `C1Jet.const_mul`, `C1Jet.congr`,
* `C1Jet.sin_sq` (the angular factor `sin²θ`, whose `z`-derivative vanishes),

and then `zderiv_N` itself, whose proof replicates the bookkeeping of `Der.jet_N`
(the `Jet`-closure of `N`) through the `z`-derivative clause.

**Trap (re-confirmed here).** Inside the proof of the closure lemmas, one must match
`HasDerivAt`-terms obtained from `C1Jet.zderiv` (elaborated in `Der.Defs`) against freshly
elaborated goals: `simpa only [Pi.add_apply]` / `Pi.neg_apply` fails on the (diamond) instance
arguments of `HasDerivAt`, while the plain `exact hda.add hdb` (`exact hd.neg`, …) works, the
two `Pi`-instances being definitionally equal on the nose.  Also
`HasDerivAt.congr_of_eventuallyEq` expects the eventual equality in the direction
`g =ᶠ f` (i.e. the *new* function on the left).
-/

set_option autoImplicit false
set_option linter.unusedVariables false

namespace Work.FTS.RegPkgGal

/-- **`C1Jet` is closed under addition**, with the sum of the constants. -/
theorem C1Jet.add {α S N₁ N₂ : ℝ} {a b : ℝ → ℝ → ℝ → ℝ} (Ha : C1Jet α S N₁ a)
    (Hb : C1Jet α S N₂ b) :
    C1Jet α S (N₁ + N₂) (fun z θ τ => a z θ τ + b z θ τ) := by
  refine ⟨Ha.jet.add Hb.jet, ?_⟩
  intro τ hτ θ hθ z hz
  obtain ⟨da, hda, hdab⟩ := Ha.zderiv τ hτ θ hθ z hz
  obtain ⟨db, hdb, hdbb⟩ := Hb.zderiv τ hτ θ hθ z hz
  exact ⟨da + db, hda.add hdb, by
    calc |da + db| ≤ |da| + |db| := abs_add_le _ _
      _ ≤ N₁ + N₂ := add_le_add hdab hdbb⟩

/-- **`C1Jet` is closed under negation**, with the same constant. -/
theorem C1Jet.neg {α S N : ℝ} {h : ℝ → ℝ → ℝ → ℝ} (H : C1Jet α S N h) :
    C1Jet α S N (fun z θ τ => -h z θ τ) := by
  refine ⟨H.jet.neg, ?_⟩
  intro τ hτ θ hθ z hz
  obtain ⟨d, hd, hdb⟩ := H.zderiv τ hτ θ hθ z hz
  exact ⟨-d, hd.neg, by simpa using hdb⟩

/-- **`C1Jet` is closed under multiplication**: the value bound is `2N₁N₂` (the `Jet.mul`
constant) and the derivative bound is *also* `2N₁N₂`, since the product rule
`(ab)' = a'b + ab'` is bounded by `N₁N₂ + N₁N₂`. -/
theorem C1Jet.mul {α S N₁ N₂ : ℝ} {a b : ℝ → ℝ → ℝ → ℝ} (Ha : C1Jet α S N₁ a)
    (Hb : C1Jet α S N₂ b) :
    C1Jet α S (2 * N₁ * N₂) (fun z θ τ => a z θ τ * b z θ τ) := by
  refine ⟨Ha.jet.mul Hb.jet, ?_⟩
  intro τ hτ θ hθ z hz
  obtain ⟨da, hda, hdab⟩ := Ha.zderiv τ hτ θ hθ z hz
  obtain ⟨db, hdb, hdbb⟩ := Hb.zderiv τ hτ θ hθ z hz
  have hza : 0 ≤ z := hz.le
  have hba : |a z θ τ| ≤ N₁ := Ha.jet.abs_le hza hθ hτ
  have hbb : |b z θ τ| ≤ N₂ := Hb.jet.abs_le hza hθ hτ
  exact ⟨da * b z θ τ + a z θ τ * db, hda.mul hdb, by
    calc |da * b z θ τ + a z θ τ * db|
        ≤ |da * b z θ τ| + |a z θ τ * db| := abs_add_le _ _
      _ = |da| * |b z θ τ| + |a z θ τ| * |db| := by rw [abs_mul, abs_mul]
      _ ≤ N₁ * N₂ + N₁ * N₂ := by
          exact add_le_add (mul_le_mul hdab hbb (abs_nonneg _) Ha.jet.nonneg)
            (mul_le_mul hba hdbb (abs_nonneg _) Ha.jet.nonneg)
      _ = 2 * N₁ * N₂ := by ring⟩

/-- **`C1Jet` is closed under scalar multiplication**, with constant `|c|·N` (the `Jet`
part is `Der.jetN_const_mul`). -/
theorem C1Jet.const_mul {α S N c : ℝ} {h : ℝ → ℝ → ℝ → ℝ} (H : C1Jet α S N h) :
    C1Jet α S (|c| * N) (fun z θ τ => c * h z θ τ) := by
  refine ⟨Work.FTS.RegPkgGal.Der.jetN_const_mul H.jet, ?_⟩
  intro τ hτ θ hθ z hz
  obtain ⟨d, hd, hdb⟩ := H.zderiv τ hτ θ hθ z hz
  exact ⟨c * d, by simpa using hd.const_mul c, by
    rw [abs_mul]
    exact mul_le_mul_of_nonneg_left hdb (abs_nonneg c)⟩

/-- **`C1Jet` transports along a pointwise equality on the strip** (the `z`-derivative clause
by `HasDerivAt.congr_of_eventuallyEq`, using that `Ioi 0` is a neighbourhood of each of its
points). -/
theorem C1Jet.congr {α S N : ℝ} {a b : ℝ → ℝ → ℝ → ℝ} (Ha : C1Jet α S N a)
    (h : ∀ z θ τ : ℝ, 0 ≤ z → θ ∈ Work.Spaces.Iθ → τ ∈ Set.Icc 0 S → a z θ τ = b z θ τ) :
    C1Jet α S N b := by
  refine ⟨Ha.jet.congr h, ?_⟩
  intro τ hτ θ hθ z hz
  obtain ⟨d, hd, hdb⟩ := Ha.zderiv τ hτ θ hθ z hz
  refine ⟨d, hd.congr_of_eventuallyEq ?_, hdb⟩
  filter_upwards [IsOpen.mem_nhds isOpen_Ioi hz] with z' hz'
  exact (h z' θ τ hz'.le hθ hτ).symm

/-- The angular factor `θ ↦ sin²θ` is a `C1Jet` of constant `4` (`z`-independent, so the
derivative bound is trivial and the `Jet` part is `Der.jetN_sin_sq`). -/
theorem C1Jet.sin_sq {α S : ℝ} (hα : 0 < α) (hα1 : α ≤ 1) :
    C1Jet α S 4 (fun _ θ _ => Real.sin θ ^ 2) := by
  refine ⟨Work.FTS.RegPkgGal.Der.jetN_sin_sq hα hα1, ?_⟩
  intro τ hτ θ hθ z hz
  exact ⟨0, hasDerivAt_const z (Real.sin θ ^ 2), by norm_num⟩

end Work.FTS.RegPkgGal

namespace Work.FTS.RegPkgGal.Der

theorem zderiv_N {α S : ℝ} {g Φ : ℝ → ℝ → ℝ → ℝ} {N₁ N₂ N₃ N₄ N₅ N₆ N₇ : ℝ}
    (hα : 0 < α) (hα13 : α ≤ 1 / 3) (hS : 0 < S)
    (hF : Work.FTS.RegPkgGal.C1Jet α S N₁ (fun z θ τ => Work.Construction.Ftau
      (Work.FTS.Regularity.pExp α) g τ z θ))
    (hDthF : Work.FTS.RegPkgGal.C1Jet α S N₂ (fun z θ τ => Work.Spaces.Dth
      (fun z θ => Work.Construction.Ftau (Work.FTS.Regularity.pExp α) g τ z θ) z θ))
    (hDzF : Work.FTS.RegPkgGal.C1Jet α S N₃ (fun z θ τ => Work.Spaces.Dz
      (fun z θ => Work.Construction.Ftau (Work.FTS.Regularity.pExp α) g τ z θ) z θ))
    (hRop : Work.FTS.RegPkgGal.C1Jet α S N₄ (fun z θ τ => Work.Construction.Rop
      (Work.FTS.Regularity.pExp α) (Work.Construction.PhiTil (Work.FTS.Regularity.pExp α)
        (Work.Construction.Ftau (Work.FTS.Regularity.pExp α) g τ)
        (Work.FTS.Regularity.gSlice Φ τ)) z θ))
    (hUopF : Work.FTS.RegPkgGal.C1Jet α S N₅ (fun z θ τ => Work.Construction.Uop
      (Work.FTS.Regularity.pExp α) (Work.Construction.PhiTil (Work.FTS.Regularity.pExp α)
        (Work.Construction.Ftau (Work.FTS.Regularity.pExp α) g τ)
        (Work.FTS.Regularity.gSlice Φ τ)) z θ
      * Work.Spaces.pth (fun z θ => Work.Construction.Ftau (Work.FTS.Regularity.pExp α)
        g τ z θ) z θ))
    (hVop : Work.FTS.RegPkgGal.C1Jet α S N₆ (fun z θ τ => Work.Construction.Vop
      (Work.Construction.PhiTil (Work.FTS.Regularity.pExp α)
        (Work.Construction.Ftau (Work.FTS.Regularity.pExp α) g τ)
        (Work.FTS.Regularity.gSlice Φ τ)) z θ))
    (hFK : Work.FTS.RegPkgGal.C1Jet α S N₇ (fun z θ τ =>
      Work.Construction.FK (Work.Construction.Ftau (Work.FTS.Regularity.pExp α) g τ) z)) :
    ∃ Nc : ℝ, Work.FTS.RegPkgGal.C1Jet α S Nc
      (fun z θ τ => Work.Construction.N (Work.FTS.Regularity.pExp α)
        (Work.Construction.Ftau (Work.FTS.Regularity.pExp α) g τ)
        (Work.FTS.Regularity.gSlice Φ τ) z θ) := by
  have hα1 : α ≤ 1 := by linarith
  have hTh : Work.FTS.RegPkgGal.C1Jet α S 4 (fun _ θ _ => Real.sin θ ^ 2) :=
    Work.FTS.RegPkgGal.C1Jet.sin_sq hα hα1
  have hT1 : Work.FTS.RegPkgGal.C1Jet α S (|(2:ℝ)| * (2 * N₄ * N₁))
      (fun z θ τ => 2 * (Work.Construction.Rop (Work.FTS.Regularity.pExp α)
        (Work.Construction.PhiTil (Work.FTS.Regularity.pExp α)
          (Work.Construction.Ftau (Work.FTS.Regularity.pExp α) g τ)
          (Work.FTS.Regularity.gSlice Φ τ)) z θ
        * Work.Construction.Ftau (Work.FTS.Regularity.pExp α) g τ z θ)) :=
    Work.FTS.RegPkgGal.C1Jet.const_mul (c := (2:ℝ))
      (Work.FTS.RegPkgGal.C1Jet.mul hRop hF)
  have hT2 : Work.FTS.RegPkgGal.C1Jet α S (|(2:ℝ)| * N₅)
      (fun z θ τ => 2 * (Work.Construction.Uop (Work.FTS.Regularity.pExp α)
        (Work.Construction.PhiTil (Work.FTS.Regularity.pExp α)
          (Work.Construction.Ftau (Work.FTS.Regularity.pExp α) g τ)
          (Work.FTS.Regularity.gSlice Φ τ)) z θ
        * Work.Spaces.pth (fun z θ => Work.Construction.Ftau (Work.FTS.Regularity.pExp α)
          g τ z θ) z θ)) :=
    Work.FTS.RegPkgGal.C1Jet.const_mul (c := (2:ℝ)) hUopF
  have hT3 : Work.FTS.RegPkgGal.C1Jet α S
      (|2 * Work.FTS.Regularity.pExp α| * (2 * N₆ * N₃))
      (fun z θ τ => 2 * Work.FTS.Regularity.pExp α * (Work.Construction.Vop
        (Work.Construction.PhiTil (Work.FTS.Regularity.pExp α)
          (Work.Construction.Ftau (Work.FTS.Regularity.pExp α) g τ)
          (Work.FTS.Regularity.gSlice Φ τ)) z θ
        * Work.Spaces.Dz (fun z θ => Work.Construction.Ftau (Work.FTS.Regularity.pExp α)
          g τ z θ) z θ)) :=
    Work.FTS.RegPkgGal.C1Jet.const_mul (c := 2 * Work.FTS.Regularity.pExp α)
      (Work.FTS.RegPkgGal.C1Jet.mul hVop hDzF)
  have hT4 : Work.FTS.RegPkgGal.C1Jet α S (|(1/2:ℝ)| * (2 * N₇ * N₂))
      (fun z θ τ => (1/2) * (Work.Construction.FK (Work.Construction.Ftau
          (Work.FTS.Regularity.pExp α) g τ) z
        * Work.Spaces.Dth (fun z θ => Work.Construction.Ftau (Work.FTS.Regularity.pExp α)
          g τ z θ) z θ)) :=
    Work.FTS.RegPkgGal.C1Jet.const_mul (c := (1/2:ℝ))
      (Work.FTS.RegPkgGal.C1Jet.mul hFK hDthF)
  have hT5 : Work.FTS.RegPkgGal.C1Jet α S (|(1:ℝ)| * (2 * 4 * (2 * N₇ * N₁)))
      (fun z θ τ => 1 * (Real.sin θ ^ 2 * (Work.Construction.FK (Work.Construction.Ftau
          (Work.FTS.Regularity.pExp α) g τ) z
        * Work.Construction.Ftau (Work.FTS.Regularity.pExp α) g τ z θ))) :=
    Work.FTS.RegPkgGal.C1Jet.const_mul (c := (1:ℝ))
      (Work.FTS.RegPkgGal.C1Jet.mul hTh (Work.FTS.RegPkgGal.C1Jet.mul hFK hF))
  have hcomb := Work.FTS.RegPkgGal.C1Jet.add
    (Work.FTS.RegPkgGal.C1Jet.add
      (Work.FTS.RegPkgGal.C1Jet.add
        (Work.FTS.RegPkgGal.C1Jet.add hT1 (Work.FTS.RegPkgGal.C1Jet.neg hT2))
        (Work.FTS.RegPkgGal.C1Jet.neg hT3))
      (Work.FTS.RegPkgGal.C1Jet.neg hT4))
    (Work.FTS.RegPkgGal.C1Jet.neg hT5)
  exact ⟨_, hcomb.congr (fun z θ τ hz hθ hτ => by
    simp only [Work.Construction.N, Work.Spaces.Dth, Work.Construction.s2]
    ring)⟩

end Work.FTS.RegPkgGal.Der
