import Mathlib
import Submission.Work.Tower.Shafarevich.Defs

/-!
# The Koch transfer lemma: vocabulary

Let `π : G →* Q` be a surjective homomorphism of groups with kernel `N = ker π`, and let
`σ : Q → G` be a section of `π`.  This file fixes the vocabulary of the proof that the
*inflation* map

`inf : H²(Q, 𝔽_p) → H²(G, 𝔽_p)`

has kernel of `𝔽_p`-dimension at most the number of generators of `N` — Koch's transfer
estimate, the group-theoretic input of Shafarevich's tower argument.

Concretely:

* `Work.CFT.KochTransfer.precompFun` — precomposition of a function `Q × Q → 𝔽_p` with `π`;
* `Work.CFT.KochTransfer.precompCocycle` — its restriction to the `2`-cocycles;
* `Work.CFT.KochTransfer.infl` — the induced map `H²(Q, 𝔽_p) → H²(G, 𝔽_p)`;
* `Work.CFT.KochTransfer.invariantHoms π` — the `𝔽_p`-space of additive maps `ker π → 𝔽_p`
  which are invariant under conjugation by `G`;
* `Work.CFT.KochTransfer.auxFun π σ hσ t` — the function `G → 𝔽_p`
  `g ↦ t (g * σ (π g))⁻¹`;
* `Work.CFT.KochTransfer.candidate π σ hσ t` — the `2`-cocycle candidate on `Q`
  `(x, y) ↦ - t (σ x * σ y * σ (x * y)⁻¹)` attached to an invariant hom `t`.

The transgression `H¹(N, 𝔽_p)^G → H²(Q, 𝔽_p)` of the extension is then
`t ↦ H²π (candidate π σ hσ t)`, and `auxFun_d12_eq` states that the inflation of `candidate t`
is the coboundary of `auxFun t`; this is what makes `candidate t` a genuine cocycle and what
identifies the kernel of `inf` with the range of the transgression.
-/

namespace Work.CFT.KochTransfer

open groupCohomology

section Setup

variable (p : ℕ) {G : Type} {Q : Type} [Group G] [Group Q] (π : G →* Q)

/-- Conjugation of an element of `ker π` by an element of `G`. -/
def conjKer (c : G) (x : π.ker) : π.ker :=
  ⟨c * (x : G) * c⁻¹, (MonoidHom.normal_ker π).conj_mem x x.2 c⟩

@[simp] lemma conjKer_coe (c : G) (x : π.ker) : (conjKer π c x : G) = c * (x : G) * c⁻¹ := rfl

/-- The `𝔽_p`-space of additive maps `ker π → 𝔽_p` which are invariant under conjugation by
`G` (i.e. `H¹(ker π, 𝔽_p)^Q` for the conjugation action). -/
def invariantHoms : Submodule (ZMod p) (π.ker → ZMod p) where
  carrier := {t | (∀ x y : π.ker, t (x * y) = t x + t y) ∧
                  (∀ c : G, ∀ x : π.ker, t (conjKer π c x) = t x)}
  zero_mem' := ⟨fun x y => by simp, fun c x => by simp⟩
  add_mem' := by
    intro a b ha hb
    refine ⟨fun x y => ?_, fun c x => ?_⟩
    · simp only [Pi.add_apply, ha.1 x y, hb.1 x y]; abel
    · simp only [Pi.add_apply, ha.2 c x, hb.2 c x]
  smul_mem' := by
    intro r a ha
    refine ⟨fun x y => ?_, fun c x => ?_⟩
    · simp only [Pi.smul_apply, ha.1 x y, smul_add]
    · simp only [Pi.smul_apply, ha.2 c x]

instance : CoeFun ↥(invariantHoms p π) (fun _ => π.ker → ZMod p) := ⟨Subtype.val⟩

lemma invariantHoms_mem_iff {t : π.ker → ZMod p} :
    t ∈ invariantHoms p π ↔ (∀ x y : π.ker, t (x * y) = t x + t y) ∧
      (∀ c : G, ∀ x : π.ker, t (conjKer π c x) = t x) := Iff.rfl

@[simp] lemma invariantHoms_add (t : invariantHoms p π) (x y : π.ker) :
    t (x * y) = t x + t y := t.2.1 x y

@[simp] lemma invariantHoms_conj (t : invariantHoms p π) (c : G) (x : π.ker) :
    t (conjKer π c x) = t x := t.2.2 c x

lemma invariantHoms_one (t : invariantHoms p π) : t 1 = 0 := by
  have h : t (1 * 1) = t 1 + t 1 := invariantHoms_add p π t 1 1
  rw [mul_one] at h
  have h2 : t 1 + 0 = t 1 + t 1 := by rw [add_zero]; exact h
  exact (add_left_cancel h2).symm

/-- The `2`-cocycle candidate on `Q` attached to an invariant hom `t` and a section `σ`. -/
def candidate (σ : Q → G) (hσ : ∀ q, π (σ q) = q) (t : invariantHoms p π) :
    Q × Q → ZMod p :=
  fun x => - t ⟨σ x.1 * σ x.2 * (σ (x.1 * x.2))⁻¹, by
    rw [MonoidHom.mem_ker, map_mul, map_mul, map_inv, hσ, hσ, hσ]
    simp⟩

/-- The function `G → 𝔽_p`, `g ↦ t (g * σ (π g))⁻¹`, attached to an invariant hom `t`. -/
def auxFun (σ : Q → G) (hσ : ∀ q, π (σ q) = q) (t : invariantHoms p π) : G → ZMod p :=
  fun g => t ⟨g * (σ (π g))⁻¹, by
    rw [MonoidHom.mem_ker, map_mul, map_inv, hσ]
    simp⟩

@[simp] lemma candidate_apply (σ : Q → G) (hσ : ∀ q, π (σ q) = q) (t : invariantHoms p π)
    (x y : Q) :
    candidate p π σ hσ t (x, y) = - t ⟨σ x * σ y * (σ (x * y))⁻¹, by
      rw [MonoidHom.mem_ker, map_mul, map_mul, map_inv, hσ, hσ, hσ]
      simp⟩ := rfl

@[simp] lemma auxFun_apply (σ : Q → G) (hσ : ∀ q, π (σ q) = q) (t : invariantHoms p π)
    (g : G) :
    auxFun p π σ hσ t g = t ⟨g * (σ (π g))⁻¹, by
      rw [MonoidHom.mem_ker, map_mul, map_inv, hσ]
      simp⟩ := rfl

end Setup

section Precomp

variable {p : ℕ} {G : Type} {Q : Type} [Group G] [Group Q] (π : G →* Q)

/-- Precomposition of a function `Q × Q → 𝔽_p` with `π`. -/
def precompFun : (Q × Q → ZMod p) →ₗ[ZMod p] (G × G → ZMod p) where
  toFun f x := f (π x.1, π x.2)
  map_add' f g := by funext x; rfl
  map_smul' c f := by funext x; rfl

@[simp] lemma precompFun_apply (f : Q × Q → ZMod p) (x : G × G) :
    precompFun π f x = f (π x.1, π x.2) := rfl

lemma precompFun_mem_cocycles {f : Q × Q → ZMod p}
    (hf : f ∈ cocycles₂ (Rep.trivial (ZMod p) Q (ZMod p))) :
    precompFun π f ∈ cocycles₂ (Rep.trivial (ZMod p) G (ZMod p)) := by
  rw [mem_cocycles₂_iff] at hf ⊢
  intro a b c
  have h := hf (π a) (π b) (π c)
  simpa [precompFun_apply, map_mul] using h

lemma precompFun_mem_cocycles_iff (hπ : Function.Surjective π) (f : Q × Q → ZMod p) :
    precompFun π f ∈ cocycles₂ (Rep.trivial (ZMod p) G (ZMod p)) ↔
      f ∈ cocycles₂ (Rep.trivial (ZMod p) Q (ZMod p)) := by
  refine ⟨?_, precompFun_mem_cocycles π⟩
  intro hf
  rw [mem_cocycles₂_iff] at hf ⊢
  intro x y z
  obtain ⟨X, hX⟩ := hπ x
  obtain ⟨Y, hY⟩ := hπ y
  obtain ⟨Z, hZ⟩ := hπ z
  have h := hf X Y Z
  simpa [precompFun_apply, map_mul, ← hX, ← hY, ← hZ] using h

lemma precompFun_injective (hπ : Function.Surjective π) :
    Function.Injective (precompFun (p := p) π) := by
  intro f h hfh
  funext x
  obtain ⟨X, hX⟩ := hπ x.1
  obtain ⟨Y, hY⟩ := hπ x.2
  have := congr_fun hfh (X, Y)
  simpa [precompFun_apply, hX, hY] using this

lemma precompFun_mem_coboundaries {f : Q × Q → ZMod p}
    (hf : f ∈ coboundaries₂ (Rep.trivial (ZMod p) Q (ZMod p))) :
    precompFun π f ∈ coboundaries₂ (Rep.trivial (ZMod p) G (ZMod p)) := by
  rw [coboundaries₂, LinearMap.mem_range] at hf
  obtain ⟨b, hb⟩ := hf
  refine LinearMap.mem_range.mpr ⟨b ∘ π, ?_⟩
  funext x
  obtain ⟨g, h⟩ := x
  have hbg := congr_fun hb (π g, π h)
  simpa [d₁₂_hom_apply, precompFun_apply, Function.comp_apply, map_mul] using hbg

/-- Precomposition of `2`-cocycles along `π`. -/
def precompCocycle : cocycles₂ (Rep.trivial (ZMod p) Q (ZMod p)) →ₗ[ZMod p]
    cocycles₂ (Rep.trivial (ZMod p) G (ZMod p)) :=
  ((precompFun π).comp (cocycles₂ (Rep.trivial (ZMod p) Q (ZMod p))).subtype).codRestrict _
    (fun f => precompFun_mem_cocycles π f.2)

@[simp] lemma precompCocycle_apply (f : cocycles₂ (Rep.trivial (ZMod p) Q (ZMod p))) :
    ((precompCocycle π f : cocycles₂ (Rep.trivial (ZMod p) G (ZMod p))) : G × G → ZMod p) =
      precompFun π (f : Q × Q → ZMod p) := rfl

/-- The inflation map `H²(Q, 𝔽_p) → H²(G, 𝔽_p)` induced by `π`. -/
noncomputable def infl : H2 (Rep.trivial (ZMod p) Q (ZMod p)) →ₗ[ZMod p]
    H2 (Rep.trivial (ZMod p) G (ZMod p)) :=
  have hle : LinearMap.ker (H2π (Rep.trivial (ZMod p) Q (ZMod p))).hom ≤
      LinearMap.ker ((H2π (Rep.trivial (ZMod p) G (ZMod p))).hom.comp (precompCocycle π)) := by
    intro x hx
    simp only [LinearMap.mem_ker, LinearMap.comp_apply] at hx ⊢
    exact (H2π_eq_zero_iff (precompCocycle π x)).mpr (by
      rw [precompCocycle_apply]
      exact precompFun_mem_coboundaries π ((H2π_eq_zero_iff x).mp hx))
  (LinearMap.ker (H2π (Rep.trivial (ZMod p) Q (ZMod p))).hom).liftQ
      ((H2π (Rep.trivial (ZMod p) G (ZMod p))).hom.comp (precompCocycle π)) hle |>.comp
    (LinearMap.quotKerEquivOfSurjective (H2π (Rep.trivial (ZMod p) Q (ZMod p))).hom
      ((ModuleCat.epi_iff_surjective _).mp inferInstance)).symm.toLinearMap

lemma infl_H2π (c : cocycles₂ (Rep.trivial (ZMod p) Q (ZMod p))) :
    infl π (H2π (Rep.trivial (ZMod p) Q (ZMod p)) c) =
      H2π (Rep.trivial (ZMod p) G (ZMod p)) (precompCocycle π c) := by
  simp only [infl, LinearMap.comp_apply, LinearEquiv.coe_coe]
  rw [LinearMap.quotKerEquivOfSurjective_symm_apply]
  exact Submodule.liftQ_apply _ _ _

end Precomp

end Work.CFT.KochTransfer
