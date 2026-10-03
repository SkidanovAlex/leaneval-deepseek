import Mathlib
import Submission.Work.ORFlatness.Flat
import Submission.Work.ORFlatness.range_map_eq_ker_map
import Submission.Work.ORFlatness.injective_map_of_retract
import Submission.Work.ORFlatness.exists_retraction_of_projective_cokernel

namespace Work.ORFlatness

universe u

open TensorProduct MulOpposite

section PullbackDefs

variable {R : Type u} [Ring R]
variable {B C P : Type u} [AddCommGroup B] [Module Rᵐᵒᵖ B] [AddCommGroup C] [Module Rᵐᵒᵖ C]
  [AddCommGroup P] [Module Rᵐᵒᵖ P]

/-- The pullback (fibre product) of `g : B → C` and `ρ : P → C`, as the kernel of
`g ∘ fst - ρ ∘ snd`, a submodule of `B × P`. -/
def Pullback (g : B →ₗ[Rᵐᵒᵖ] C) (ρ : P →ₗ[Rᵐᵒᵖ] C) : Submodule Rᵐᵒᵖ (B × P) :=
  LinearMap.ker ((g.comp (LinearMap.fst Rᵐᵒᵖ B P)) -
    (ρ.comp (LinearMap.snd Rᵐᵒᵖ B P)))

theorem mem_pullback {g : B →ₗ[Rᵐᵒᵖ] C} {ρ : P →ₗ[Rᵐᵒᵖ] C} {x : B × P} :
    x ∈ Pullback g ρ ↔ g x.1 = ρ x.2 := by
  simp [Pullback, LinearMap.mem_ker, sub_eq_zero]

/-- First projection out of the pullback. -/
def Pullback.fst (g : B →ₗ[Rᵐᵒᵖ] C) (ρ : P →ₗ[Rᵐᵒᵖ] C) : Pullback g ρ →ₗ[Rᵐᵒᵖ] B :=
  (LinearMap.fst Rᵐᵒᵖ B P).comp (Pullback g ρ).subtype

/-- Second projection out of the pullback. -/
def Pullback.snd (g : B →ₗ[Rᵐᵒᵖ] C) (ρ : P →ₗ[Rᵐᵒᵖ] C) : Pullback g ρ →ₗ[Rᵐᵒᵖ] P :=
  (LinearMap.snd Rᵐᵒᵖ B P).comp (Pullback g ρ).subtype

@[simp] theorem Pullback.fst_apply (g : B →ₗ[Rᵐᵒᵖ] C) (ρ : P →ₗ[Rᵐᵒᵖ] C)
    (q : Pullback g ρ) : Pullback.fst g ρ q = q.1.1 := rfl

@[simp] theorem Pullback.snd_apply (g : B →ₗ[Rᵐᵒᵖ] C) (ρ : P →ₗ[Rᵐᵒᵖ] C)
    (q : Pullback g ρ) : Pullback.snd g ρ q = q.1.2 := rfl

/-- The map `A → Pullback g ρ`, `a ↦ (f a, 0)`, when `g ∘ f = 0`. -/
def Pullback.liftFst {A : Type u} [AddCommGroup A] [Module Rᵐᵒᵖ A]
    (g : B →ₗ[Rᵐᵒᵖ] C) (ρ : P →ₗ[Rᵐᵒᵖ] C) (f : A →ₗ[Rᵐᵒᵖ] B)
    (hf : ∀ a, g (f a) = 0) : A →ₗ[Rᵐᵒᵖ] Pullback g ρ where
  toFun a := ⟨(f a, 0), by rw [mem_pullback]; simp [hf a]⟩
  map_add' a a' := by
    apply Subtype.ext
    simp [map_add]
  map_smul' r a := by
    apply Subtype.ext
    simp [map_smul]

/-- The map `K → Pullback g ρ`, `k ↦ (0, ι k)`, when `ρ ∘ ι = 0`. -/
def Pullback.liftSnd {K : Type u} [AddCommGroup K] [Module Rᵐᵒᵖ K]
    (g : B →ₗ[Rᵐᵒᵖ] C) (ρ : P →ₗ[Rᵐᵒᵖ] C) (ι : K →ₗ[Rᵐᵒᵖ] P)
    (hι : ∀ k, ρ (ι k) = 0) : K →ₗ[Rᵐᵒᵖ] Pullback g ρ where
  toFun k := ⟨(0, ι k), by rw [mem_pullback]; simp [hι k]⟩
  map_add' k k' := by
    apply Subtype.ext
    simp [map_add]
  map_smul' r k := by
    apply Subtype.ext
    simp [map_smul]

@[simp] theorem Pullback.fst_liftFst {A : Type u} [AddCommGroup A] [Module Rᵐᵒᵖ A]
    (g : B →ₗ[Rᵐᵒᵖ] C) (ρ : P →ₗ[Rᵐᵒᵖ] C) (f : A →ₗ[Rᵐᵒᵖ] B) (hf : ∀ a, g (f a) = 0) :
    (Pullback.fst g ρ).comp (Pullback.liftFst g ρ f hf) = f := by
  ext a
  simp [Pullback.liftFst]

@[simp] theorem Pullback.snd_liftFst {A : Type u} [AddCommGroup A] [Module Rᵐᵒᵖ A]
    (g : B →ₗ[Rᵐᵒᵖ] C) (ρ : P →ₗ[Rᵐᵒᵖ] C) (f : A →ₗ[Rᵐᵒᵖ] B) (hf : ∀ a, g (f a) = 0) :
    (Pullback.snd g ρ).comp (Pullback.liftFst g ρ f hf) = 0 := by
  ext a
  simp [Pullback.liftFst]

@[simp] theorem Pullback.fst_liftSnd {K : Type u} [AddCommGroup K] [Module Rᵐᵒᵖ K]
    (g : B →ₗ[Rᵐᵒᵖ] C) (ρ : P →ₗ[Rᵐᵒᵖ] C) (ι : K →ₗ[Rᵐᵒᵖ] P) (hι : ∀ k, ρ (ι k) = 0) :
    (Pullback.fst g ρ).comp (Pullback.liftSnd g ρ ι hι) = 0 := by
  ext k
  simp [Pullback.liftSnd]

@[simp] theorem Pullback.snd_liftSnd {K : Type u} [AddCommGroup K] [Module Rᵐᵒᵖ K]
    (g : B →ₗ[Rᵐᵒᵖ] C) (ρ : P →ₗ[Rᵐᵒᵖ] C) (ι : K →ₗ[Rᵐᵒᵖ] P) (hι : ∀ k, ρ (ι k) = 0) :
    (Pullback.snd g ρ).comp (Pullback.liftSnd g ρ ι hι) = ι := by
  ext k
  simp [Pullback.liftSnd]

theorem Pullback.liftFst_injective {A : Type u} [AddCommGroup A] [Module Rᵐᵒᵖ A]
    (g : B →ₗ[Rᵐᵒᵖ] C) (ρ : P →ₗ[Rᵐᵒᵖ] C) (f : A →ₗ[Rᵐᵒᵖ] B) (hf : ∀ a, g (f a) = 0)
    (hinj : Function.Injective f) : Function.Injective (Pullback.liftFst g ρ f hf) := by
  intro a a' h
  apply hinj
  have h2 : (f a, (0 : P)) = (f a', 0) := congrArg Subtype.val h
  exact (Prod.mk.injEq _ _ _ _).mp h2 |>.1

theorem Pullback.snd_surjective (g : B →ₗ[Rᵐᵒᵖ] C) (ρ : P →ₗ[Rᵐᵒᵖ] C)
    (hg : Function.Surjective g) : Function.Surjective (Pullback.snd g ρ) := by
  intro p
  obtain ⟨b, hb⟩ := hg (ρ p)
  exact ⟨⟨(b, p), by rw [mem_pullback]; exact hb⟩, rfl⟩

theorem Pullback.fst_surjective (g : B →ₗ[Rᵐᵒᵖ] C) (ρ : P →ₗ[Rᵐᵒᵖ] C)
    (hρ : Function.Surjective ρ) : Function.Surjective (Pullback.fst g ρ) := by
  intro b
  obtain ⟨p, hp⟩ := hρ (g b)
  exact ⟨⟨(b, p), by rw [mem_pullback]; exact hp.symm⟩, rfl⟩

theorem Pullback.ker_snd_eq_range_liftFst {A : Type u} [AddCommGroup A] [Module Rᵐᵒᵖ A]
    (g : B →ₗ[Rᵐᵒᵖ] C) (ρ : P →ₗ[Rᵐᵒᵖ] C) (f : A →ₗ[Rᵐᵒᵖ] B) (hf : ∀ a, g (f a) = 0)
    (hfr : f.range = g.ker) :
    (Pullback.liftFst g ρ f hf).range = (Pullback.snd g ρ).ker := by
  ext q
  constructor
  · intro hq
    obtain ⟨a, ha⟩ := hq
    rw [← ha, LinearMap.mem_ker]
    simp [Pullback.liftFst]
  · intro hq
    rw [LinearMap.mem_ker] at hq
    have hq2 : q.1.2 = 0 := by simpa using hq
    have hmem : q.1 ∈ Pullback g ρ := q.2
    rw [mem_pullback] at hmem
    have hb : q.1.1 ∈ f.range := by
      rw [hfr, LinearMap.mem_ker]
      rw [hq2, map_zero] at hmem
      exact hmem
    obtain ⟨a, ha⟩ := hb
    refine ⟨a, ?_⟩
    apply Subtype.ext
    show (f a, (0 : P)) = q.1
    rw [ha]
    exact Prod.ext rfl hq2.symm

theorem Pullback.ker_fst_eq_range_liftSnd (g : B →ₗ[Rᵐᵒᵖ] C) (ρ : P →ₗ[Rᵐᵒᵖ] C) :
    (Pullback.liftSnd g ρ (Submodule.subtype (LinearMap.ker ρ)) (fun k => k.2)).range
      = (Pullback.fst g ρ).ker := by
  ext q
  constructor
  · rintro ⟨k, rfl⟩
    rw [LinearMap.mem_ker]
    simp [Pullback.liftSnd]
  · intro hq
    rw [LinearMap.mem_ker] at hq
    have hq1 : q.1.1 = 0 := by simpa using hq
    have hmem : q.1 ∈ Pullback g ρ := q.2
    rw [mem_pullback] at hmem
    rw [hq1, map_zero] at hmem
    have hk : q.1.2 ∈ LinearMap.ker ρ := LinearMap.mem_ker.mpr hmem.symm
    refine ⟨⟨q.1.2, hk⟩, ?_⟩
    apply Subtype.ext
    show ((0 : B), q.1.2) = q.1
    rw [← hq1]

end PullbackDefs


namespace BalTensor

theorem map_zero {R : Type u} [Ring R] {X : Type u} [AddCommGroup X] [Module Rᵐᵒᵖ X]
    {X' : Type u} [AddCommGroup X'] [Module Rᵐᵒᵖ X'] {N : Type u} [AddCommGroup N] [Module R N]
    {N' : Type u} [AddCommGroup N'] [Module R N'] (g : N →ₗ[R] N') :
    map R (0 : X →ₗ[Rᵐᵒᵖ] X') g = 0 := by
  refine BalTensor.ext R ?_
  intro x n
  simp

end BalTensor

/-- The converse direction of dimension shifting: if `0 → A →f B →g C → 0` is a short
exact sequence of right `R`-modules (`f` injective, `g` surjective, `f.range = g.ker`)
and `Tor1Vanishes R C N`, then the induced map `A ⊗[R] N → B ⊗[R] N` is injective.

Proof sketch: take the witness `P : ProjPres R C` of `hC`, covering map `ρ : P.P →ₗ C`,
`K := LinearMap.ker ρ`, so `K ⊗ N → P.P ⊗ N` is injective.  Form the pullback
`Q := {p : B × P.P // g p.1 = ρ p.2} ⊆ B × P.P`.  Then the two projections give short
exact sequences `0 → A → Q → P.P → 0` and `0 → K → Q → B → 0`.  Since `P.P` is projective,
`0 → A → Q → P.P → 0` splits, so the inclusion `A ↪ Q` has a retraction `r`, and hence
`BalTensor.map R (A ↪ Q) id` is injective (a split injection tensored with an identity is
injective: `(map r id).comp (map ι id) = map (r.comp ι) id = id` by
`BalTensor.map_comp` and `BalTensor.map_id`).
Let `x` be in the kernel of `BalTensor.map R f id`; its image `x̃ ∈ BalTensor R Q N` lies
in the kernel of `BalTensor.map R (Q → B) id`, which by right exactness
(`Work.ORFlatness.range_map_eq_ker_map`, applied to `K → Q → B → 0`) equals the range of
`BalTensor.map R (K ↪ Q) id`, so `x̃ = (map (K ↪ Q) id) w` for some `w`.  The image of `x`
under `A → Q → P.P` is `0` (because `A = ker (Q → P.P)`), and the composite `K → Q → P.P`
is the inclusion `K ↪ P.P`; hence `(map (K ↪ P.P) id) w = 0`, so `w = 0` by the choice of
`P`, hence `x̃ = 0`; since `A ↪ Q` is split injective, `x = 0`. -/
theorem injective_of_tor1Vanishes {R : Type u} [Ring R] {A B C : Type u}
    [AddCommGroup A] [Module Rᵐᵒᵖ A] [AddCommGroup B] [Module Rᵐᵒᵖ B]
    [AddCommGroup C] [Module Rᵐᵒᵖ C]
    (f : A →ₗ[Rᵐᵒᵖ] B) (g : B →ₗ[Rᵐᵒᵖ] C) (hf : Function.Injective f)
    (hg : Function.Surjective g) (hfg : f.range = g.ker)
    (N : Type u) [AddCommGroup N] [Module R N]
    (hC : Work.ORFlatness.Tor1Vanishes R C N) :
    Function.Injective
      (Work.ORFlatness.BalTensor.map R f (LinearMap.id : N →ₗ[R] N)) := by

  obtain ⟨P, hK⟩ := hC
  have hρ : Function.Surjective P.π := P.surj
  have hf0 : ∀ a, g (f a) = 0 := fun a => by
    have h : f a ∈ g.ker := by rw [← hfg]; exact LinearMap.mem_range_self f a
    simpa using h
  let ιA : A →ₗ[Rᵐᵒᵖ] Pullback g P.π := Pullback.liftFst g P.π f hf0
  let ιK : LinearMap.ker P.π →ₗ[Rᵐᵒᵖ] Pullback g P.π :=
    Pullback.liftSnd g P.π (Submodule.subtype (LinearMap.ker P.π)) (fun k => k.2)
  obtain ⟨r, hr⟩ := exists_retraction_of_projective_cokernel ιA (Pullback.snd g P.π)
    (Pullback.liftFst_injective g P.π f hf0 hf)
    (Pullback.snd_surjective g P.π hg)
    (Pullback.ker_snd_eq_range_liftFst g P.π f hf0 hfg)
  have hinjA : Function.Injective (BalTensor.map R ιA (LinearMap.id : N →ₗ[R] N)) :=
    injective_map_of_retract ιA r hr N
  have hker : (BalTensor.map R ιK (LinearMap.id : N →ₗ[R] N)).range
      = (BalTensor.map R (Pullback.fst g P.π) (LinearMap.id : N →ₗ[R] N)).ker :=
    range_map_eq_ker_map ιK (Pullback.fst g P.π)
      (Pullback.fst_surjective g P.π hρ)
      (Pullback.ker_fst_eq_range_liftSnd g P.π) N
  have hfstA : (BalTensor.map R f (LinearMap.id : N →ₗ[R] N))
      = (BalTensor.map R (Pullback.fst g P.π) (LinearMap.id : N →ₗ[R] N)).comp
        (BalTensor.map R ιA (LinearMap.id : N →ₗ[R] N)) := by
    rw [← BalTensor.map_comp]
    have h1 : (Pullback.fst g P.π).comp ιA = f := Pullback.fst_liftFst g P.π f hf0
    rw [h1]
    simp
  have hsndA : (BalTensor.map R (Pullback.snd g P.π) (LinearMap.id : N →ₗ[R] N)).comp
        (BalTensor.map R ιA (LinearMap.id : N →ₗ[R] N)) = 0 := by
    rw [← BalTensor.map_comp]
    have h1 : (Pullback.snd g P.π).comp ιA = 0 := Pullback.snd_liftFst g P.π f hf0
    rw [h1]
    simp [BalTensor.map_zero]
  have hsndK : (BalTensor.map R (Pullback.snd g P.π) (LinearMap.id : N →ₗ[R] N)).comp
        (BalTensor.map R ιK (LinearMap.id : N →ₗ[R] N))
      = BalTensor.map R (Submodule.subtype (LinearMap.ker P.π)) (LinearMap.id : N →ₗ[R] N) := by
    rw [← BalTensor.map_comp]
    have h1 : (Pullback.snd g P.π).comp ιK = Submodule.subtype (LinearMap.ker P.π) :=
      Pullback.snd_liftSnd g P.π (Submodule.subtype (LinearMap.ker P.π)) (fun k => k.2)
    rw [h1]
    simp
  intro x y hxy
  have hzf : (BalTensor.map R f (LinearMap.id : N →ₗ[R] N)) (x - y) = 0 := by
    rw [map_sub, hxy, sub_self]
  set z : BalTensor R A N := x - y with hzdef
  have hzf' : (BalTensor.map R f (LinearMap.id : N →ₗ[R] N)) z = 0 := by
    rw [hzdef]; exact hzf
  have hzfA : (BalTensor.map R (Pullback.fst g P.π) (LinearMap.id : N →ₗ[R] N))
      ((BalTensor.map R ιA (LinearMap.id : N →ₗ[R] N)) z) = 0 := by
    rw [← AddMonoidHom.comp_apply, ← hfstA]
    exact hzf'
  have hzr : (BalTensor.map R ιA (LinearMap.id : N →ₗ[R] N)) z
      ∈ (BalTensor.map R ιK (LinearMap.id : N →ₗ[R] N)).range := by
    rw [hker, AddMonoidHom.mem_ker]
    exact hzfA
  obtain ⟨w, hw⟩ := hzr
  have hsndz : (BalTensor.map R (Pullback.snd g P.π) (LinearMap.id : N →ₗ[R] N))
      ((BalTensor.map R ιA (LinearMap.id : N →ₗ[R] N)) z) = 0 := by
    rw [← AddMonoidHom.comp_apply, hsndA]
    rfl
  have hwK : BalTensor.map R (Submodule.subtype (LinearMap.ker P.π))
      (LinearMap.id : N →ₗ[R] N) w = 0 := by
    have h1 : (BalTensor.map R (Pullback.snd g P.π) (LinearMap.id : N →ₗ[R] N))
        ((BalTensor.map R ιK (LinearMap.id : N →ₗ[R] N)) w) = 0 := by
      rw [hw, hsndz]
    rw [← AddMonoidHom.comp_apply, hsndK] at h1
    exact h1
  have hw0 : w = 0 := hK (by rw [hwK]; simp)
  have hzA : (BalTensor.map R ιA (LinearMap.id : N →ₗ[R] N)) z = 0 := by
    rw [← hw, hw0]
    simp
  have hz0 : z = 0 := hinjA (show (BalTensor.map R ιA (LinearMap.id : N →ₗ[R] N)) z
      = (BalTensor.map R ιA (LinearMap.id : N →ₗ[R] N)) 0 from by rw [hzA]; simp)
  rw [hzdef] at hz0
  exact sub_eq_zero.mp hz0

end Work.ORFlatness
