import Mathlib
import Submission.Work.Interfaces.Parabolic
import Submission.Work.Horn.basic

/-!
# REPEL area: the objects of Shishikura §6

The renormalisation of Shishikura §6 turns the return map `R̃_f` of the perturbed map `f` (a lifted
`T`-equivariant map, `PertData.R`) into a new parabolic germ `ǧ = s · pushdown R̃_f(·/s)` acting on
the cylinder `ℂ/ℤ`; `ǧ` is a perturbation of the horn map `g₀ = pushdown Ẽ_{f₀}` of the unperturbed
map.  This file fixes the vocabulary (`germ1`, `Dgerm1`, `g0germ`, `s0`) and records the elementary
facts about it.
-/

namespace Work.Repel

open MandelDim Complex Set Metric Filter Topology
open Work.Horn.MandelDim

noncomputable section

/-- The rescaled pushdown of a lifted `T`-equivariant map: `ζ ↦ s * pushdown R (ζ / s)`. -/
def germ1 (s : ℂ) (R : ℂ → ℂ) : ℂ → ℂ := fun ζ => s * pushdown R (ζ / s)

/-- The natural domain of `germ1 s R`: the `s`-image of `{0} ∪ π(DR)`. -/
def Dgerm1 (s : ℂ) (DR : Set ℂ) : Set ℂ := (fun ζ => s * ζ) '' (insert 0 (piExp '' DR))

/-- The rescaling constant of the horn map of `f₀`: `s₀ = (pushdown d.E)''(0)/2`. -/
def s0 {f₀ : ℂ → ℂ} {D₀ : Set ℂ} (d : ParabData f₀ D₀) : ℂ :=
  deriv (deriv (pushdown d.E)) 0 / 2

/-- The level-1 base germ: the rescaled pushdown of the unperturbed horn map `d.E`. -/
def g0germ {f₀ : ℂ → ℂ} {D₀ : Set ℂ} (d : ParabData f₀ D₀) : ℂ → ℂ := germ1 (s0 d) d.E

/-- The domain of the level-1 base germ, as it appears in `HornData.g_F0`. -/
def Dg0germ {f₀ : ℂ → ℂ} {D₀ : Set ℂ} (d : ParabData f₀ D₀) (hd : HornData d) : Set ℂ :=
  (fun ζ => s0 d * ζ) '' (insert 0 (piExp '' (hd.Bu ∪ hd.Bl)))

@[simp]
lemma germ1_apply (s : ℂ) (R : ℂ → ℂ) (ζ : ℂ) : germ1 s R ζ = s * pushdown R (ζ / s) := rfl

lemma germ1_zero (s : ℂ) (R : ℂ → ℂ) : germ1 s R 0 = 0 := by
  rw [germ1_apply, zero_div, pushdown_zero, mul_zero]

/-- `s₀` is nonzero, by `HornData.g_second`. -/
lemma s0_ne_zero {f₀ : ℂ → ℂ} {D₀ : Set ℂ} (d : ParabData f₀ D₀) (hd : HornData d) :
    s0 d ≠ 0 := by
  unfold s0
  exact div_ne_zero hd.g_second (by norm_num)

/-- The base germ of the level-1 picture is a parabolic germ (from `HornData.g_F0`). -/
lemma g0germ_eq {f₀ : ℂ → ℂ} {D₀ : Set ℂ} (d : ParabData f₀ D₀) :
    g0germ d = fun ζ => deriv (deriv (pushdown d.E)) 0 / 2 *
      pushdown d.E (ζ / (deriv (deriv (pushdown d.E)) 0 / 2)) :=
  rfl

lemma Dg0germ_eq {f₀ : ℂ → ℂ} {D₀ : Set ℂ} (d : ParabData f₀ D₀) (hd : HornData d) :
    Dg0germ d hd = (fun ζ => deriv (deriv (pushdown d.E)) 0 / 2 * ζ) ''
      insert 0 (piExp '' (hd.Bu ∪ hd.Bl)) :=
  rfl

lemma isParabolicGerm_g0germ {f₀ : ℂ → ℂ} {D₀ : Set ℂ} (d : ParabData f₀ D₀)
    (hd : HornData d) : IsParabolicGerm (g0germ d) (Dg0germ d hd) := by
  rw [g0germ_eq d, Dg0germ_eq d hd]
  exact hd.g_F0.1


/-- The base germ of the level-1 picture is in `𝓕₀` (from `HornData.g_F0`). -/
lemma inF0_g0germ {f₀ : ℂ → ℂ} {D₀ : Set ℂ} (d : ParabData f₀ D₀) (hd : HornData d) :
    InF0 (g0germ d) (Dg0germ d hd) := by
  rw [g0germ_eq d, Dg0germ_eq d hd]
  exact hd.g_F0


/-- The hyperbolic return structure of Shishikura §6: `N` disjoint "petals" `Ω i` inside the
half-ball `ball p (r/2)`, each mapped bijectively onto the ball `ball p r` by an iterate `f^[n i]`,
with derivative bounded by `K` on `Ω i`. -/
structure ReturnData (f : ℂ → ℂ) (p : ℂ) (r K : ℝ) where
  N : ℕ
  n : Fin N → ℕ
  Ω : Fin N → Set ℂ
  u : Fin N → ℂ
  δ : Fin N → ℝ
  hN : 2 ≤ N
  hn : ∀ i, 1 ≤ n i
  hδ : ∀ i, 0 < δ i
  hΩsub : ∀ i, Ω i ⊆ ball (u i) (δ i)
  hΩhalf : ∀ i, Ω i ⊆ ball p (r / 2)
  hdisj : ∀ i j, i ≠ j → Disjoint (ball (u i) (δ i)) (ball (u j) (δ j))
  hdiff : ∀ i, DifferentiableOn ℂ (f^[n i]) (ball (u i) (δ i))
  hinj : ∀ i, InjOn (f^[n i]) (ball (u i) (δ i))
  hsurj : ∀ i, ball p r ⊆ (f^[n i]) '' (Ω i)
  hderiv : ∀ i, ∀ z ∈ Ω i, ‖deriv (f^[n i]) z‖ ≤ K

end

end Work.Repel
