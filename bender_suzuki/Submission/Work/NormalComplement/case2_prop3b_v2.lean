import Mathlib
import Submission.Work.NormalComplement.Sections
import Submission.Work.NormalComplement.Defs
import Submission.Work.NormalComplement.Prelim
import Submission.Work.NormalComplement.prop2b_conj_into_centD
import Submission.Work.NormalComplement.IsSubnormalInPgroup

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

namespace Work.NormalComplement

open Classical
open scoped Pointwise commutatorElement
open LeanEval.GroupTheory.Defs
open Submission.Blueprint

/-! ## Elementary conjugation bookkeeping

Two general facts used to transport the conclusion of Ch. II §4 Prop. 3 along the `D`-conjugation
that puts `X ≤ D` inside `V = C_D(t)` (`Work.NormalComplement.prop2b_conj_into_centD`). -/

/-- The image of a normalizer under a bijective endomorphism `f` is the normalizer of the image. -/
lemma map_normalizer_of_bijective {G : Type*} [Group G] {f : G →* G}
    (hf : Function.Bijective f) (X : Subgroup G) :
    (Subgroup.normalizer (X : Set G)).map f = Subgroup.normalizer (X.map f : Set G) := by
  refine le_antisymm (Subgroup.le_normalizer_map f) ?_
  have h1 : Subgroup.comap f (Subgroup.normalizer (X.map f : Set G)) ≤
      Subgroup.normalizer (X : Set G) := by
    intro g hg
    rw [Subgroup.mem_comap] at hg
    rw [Subgroup.mem_normalizer_iff] at hg
    rw [Subgroup.mem_normalizer_iff]
    intro x
    have key : (f g * f x * (f g)⁻¹ ∈ X.map f) ↔ (g * x * g⁻¹ ∈ X) := by
      constructor
      · rintro ⟨y, hy, hyf⟩
        have h2 : f (g * x * g⁻¹) = f y := by rw [map_mul, map_mul, map_inv, hyf]
        rw [hf.1 h2]; exact hy
      · intro h
        exact ⟨g * x * g⁻¹, h, by rw [map_mul, map_mul, map_inv]⟩
    have key2 : (f x ∈ X.map f) ↔ (x ∈ X) := by
      constructor
      · rintro ⟨y, hy, hyf⟩; rw [← hf.1 hyf]; exact hy
      · intro h; exact ⟨x, h, rfl⟩
    exact key2.symm.trans ((hg (f x)).trans key)
  calc Subgroup.normalizer (X.map f : Set G)
      = Subgroup.map f (Subgroup.comap f (Subgroup.normalizer (X.map f : Set G))) :=
        (Subgroup.map_comap_eq_self_of_surjective hf.2 _).symm
    _ ≤ Subgroup.map f (Subgroup.normalizer (X : Set G)) := Subgroup.map_mono h1

/-- The image of a centralizer under a bijective endomorphism `f` is the centralizer of the
image. -/
lemma map_centralizer_of_bijective {G : Type*} [Group G] {f : G →* G}
    (hf : Function.Bijective f) (X : Subgroup G) :
    (Subgroup.centralizer (X : Set G)).map f = Subgroup.centralizer (X.map f : Set G) := by
  refine le_antisymm ?_ ?_
  · intro z hz
    obtain ⟨g, hg, rfl⟩ := Subgroup.mem_map.mp hz
    rw [Subgroup.mem_centralizer_iff] at hg ⊢
    intro w hw
    obtain ⟨x, hx, rfl⟩ := Subgroup.mem_map.mp hw
    exact (map_mul f x g).symm.trans ((congrArg f (hg x hx)).trans (map_mul f g x))
  · intro h hh
    rw [Subgroup.mem_centralizer_iff] at hh
    obtain ⟨g, hg⟩ := hf.2 h
    refine Subgroup.mem_map.mpr ⟨g, ?_, hg⟩
    rw [Subgroup.mem_centralizer_iff]
    intro x hx
    have h1 : f (x * g) = f (g * x) := by
      rw [map_mul, map_mul, hg]
      exact hh (f x) ⟨x, hx, rfl⟩
    exact hf.1 h1

/-- Conjugation by an element of a subgroup fixes the subgroup.  (Private: `pcontrol_criterion`
has a public lemma of the same name, and both are imported by `Main`.) -/
private lemma map_conj_eq_self_of_mem {G : Type*} [Group G] {A : Subgroup G} {g : G} (hg : g ∈ A) :
    A.map (MulAut.conj g).toMonoidHom = A := by
  refine le_antisymm ?_ ?_
  · rintro x ⟨y, hy, rfl⟩
    simpa only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply] using
      A.mul_mem (A.mul_mem hg hy) (A.inv_mem hg)
  · intro x hx
    exact ⟨g⁻¹ * x * g, A.mul_mem (A.mul_mem (A.inv_mem hg) hx) hg, by
      simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]; group⟩

/-- **Peterfalvi I Ch. II §4 Prop. 3 (b)**, in the form used by Ch. III §2 Prop. 1: for a subgroup
`X ≤ D = H ∩ H^t` with three fixed points, a `p`-subgroup, and a nontrivial `Y ≤ X` normalised by
a nontrivial element of `K = J(D,t)`, the normaliser `N_H(X)` has the rank-one shape
`N_H(X) = S ⋊ N_D(X)` with `S ≤ H ⊓ C_G(X)` a `2`-subgroup and `S ⊓ D = ⊥`.

Proof.  By `prop2b_conj_into_centD` there is `d ∈ D` with `X' = d X d⁻¹ ≤ V = C_D(t)`.  Conjugating
`Y` gives `Y' = d Y d⁻¹ ≤ X'`, nonzero and subnormal in `X'` (subgroups of a `p`-group are subnormal,
`isSubnormalIn_of_isPGroup`); `hKinv` transports `k ∈ Kset D t` and `k ∈ N(Y)` to `φ k ∈ Kset D t`
and `φ k ∈ N(Y')`.  The blue-print input `ChIIFourP3SubnormalProp` applied to `(X', Y')` yields
`S' ≤ C_G(X') ⊓ H` with `H ⊓ N_G(X') = S' ⊔ (D ⊓ N_G(X'))` and `H ⊓ N_G(X') ≤ N_G(S')`; conjugating
back by `d⁻¹` (an automorphism fixing `H` and `D`) gives the conclusion. -/
theorem case2_prop3b_v2 (G : Type) [Group G] [Finite G]
    (hS : Submission.Blueprint.Situation G) (hBP : Work.NormalComplement.BenderPrelimProp)
    (hC4 : Submission.Blueprint.ChIIFourProp) (hP3 : Submission.Blueprint.ChIIFourP3SubnormalProp)
    {H : Subgroup G} (hH : LeanEval.GroupTheory.Defs.IsStronglyEmbedded H)
    {t : G} (ht : orderOf t = 2) (htH : t ∉ H)
    (hKinv : Work.NormalComplement.KInvariantUnderD H t)
    {p : ℕ} [Fact p.Prime] {X : Subgroup G} (hX : X ≤ Submission.Blueprint.twoPoint H t)
    (hXp : IsPGroup p X)
    (hX3 : 3 ≤ (Submission.Blueprint.fixedPts H X).ncard)
    {Y : Subgroup G} (hYX : Y ≤ X) (hYne : Y ≠ ⊥)
    (hkY : ∃ k ∈ Work.NormalComplement.Kset (Submission.Blueprint.twoPoint H t) t,
        k ≠ 1 ∧ k ∈ Subgroup.normalizer (Y : Set G)) :
    ∃ S : Subgroup G, IsPGroup 2 S ∧ S ≤ H ⊓ Subgroup.centralizer (X : Set G) ∧
      S ⊓ Submission.Blueprint.twoPoint H t = ⊥ ∧
      Subgroup.normalizer (X : Set G) ⊓ H ≤ Subgroup.normalizer (S : Set G) ∧
      H ⊓ Subgroup.normalizer (X : Set G) =
        S ⊔ (Submission.Blueprint.twoPoint H t ⊓ Subgroup.normalizer (X : Set G)) := by
  classical
  -- Ch. II §4 Prop. 2 (b): some `d ∈ D` sends `X` into `V = C_D(t)`.
  obtain ⟨d, hdD, hdX⟩ := prop2b_conj_into_centD G hS hBP hC4 hH ht htH hX hX3
  obtain ⟨k, hkK, hkne, hkN⟩ := hkY
  -- The conjugating automorphism `φ = conj d` and its inverse `ψ = conj d⁻¹`.
  set φ : G →* G := (MulAut.conj d).toMonoidHom with hφdef
  set ψ : G →* G := (MulAut.conj d⁻¹).toMonoidHom with hψdef
  have hψφ : ∀ x : G, ψ (φ x) = x := fun x => by
    rw [hφdef, hψdef]
    simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
    group
  have hφψ : ∀ x : G, φ (ψ x) = x := fun x => by
    rw [hφdef, hψdef]
    simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
    group
  have hφinj : Function.Injective φ := fun a b hab => by
    have h := congrArg ψ hab
    rwa [hψφ a, hψφ b] at h
  have hψinj : Function.Injective ψ := fun a b hab => by
    have h := congrArg φ hab
    rwa [hφψ a, hφψ b] at h
  have hψsurj : Function.Surjective ψ := fun x => ⟨φ x, hψφ x⟩
  have hcomp : ψ.comp φ = MonoidHom.id G := MonoidHom.ext hψφ
  -- `H` and `D` are fixed by `ψ` (as `d ∈ D ≤ H`).
  have hdH : d ∈ H := hdD.1
  have hHmap : H.map ψ = H := by
    rw [hψdef]
    exact map_conj_eq_self_of_mem (H.inv_mem hdH)
  have hDmap : (twoPoint H t).map ψ = twoPoint H t := by
    rw [hψdef]
    exact map_conj_eq_self_of_mem ((twoPoint H t).inv_mem hdD)
  have hXmap : (X.map φ).map ψ = X := by
    rw [Subgroup.map_map, hcomp, Subgroup.map_id]
  -- The transported `X' = φ X` is a subgroup of `V`.
  have hX'V : X.map φ ≤ centD H t := by
    rw [hφdef]; exact hdX
  -- `Y' = φ Y` is nontrivial and subnormal in `X'`.
  have hφker : φ.ker = ⊥ := (MonoidHom.ker_eq_bot_iff φ).mpr hφinj
  have hY'ne : Y.map φ ≠ ⊥ := by
    intro hbot
    have hle : Y ≤ φ.ker := (Subgroup.map_eq_bot_iff Y).mp hbot
    rw [hφker] at hle
    exact hYne (le_bot_iff.mp hle)
  have hY'le : Y.map φ ≤ X.map φ := Subgroup.map_mono hYX
  have hX'p : IsPGroup p (X.map φ) := hXp.map φ
  have hsub' : Submission.Blueprint.IsSubnormalIn (Y.map φ) (X.map φ) :=
    isSubnormalIn_of_isPGroup hY'le hX'p
  -- `φ k ∈ Kset D t` (via `hKinv`) normalises `Y'`.
  have hk'K : φ k ∈ Submission.Blueprint.invertedBy (Submission.Blueprint.twoPoint H t) t := by
    have h := hKinv d hdD k hkK
    simpa only [hφdef, MulEquiv.coe_toMonoidHom, MulAut.conj_apply] using h
  have hk'ne : φ k ≠ 1 := by
    intro h
    exact hkne (hφinj (by rw [h, map_one]))
  have hk'N : φ k ∈ Subgroup.normalizer (Y.map φ : Set G) := by
    rw [Subgroup.mem_normalizer_iff]
    intro y'
    constructor
    · rintro ⟨y, hy, rfl⟩
      have hky : k * y * k⁻¹ ∈ Y := (Subgroup.mem_normalizer_iff.mp hkN y).mp hy
      exact ⟨k * y * k⁻¹, hky, by rw [map_mul, map_mul, map_inv]⟩
    · rintro ⟨y, hy, hyf⟩
      have hky : k⁻¹ * y * k ∈ Y := by
        have h := (Subgroup.mem_normalizer_iff.mp (Subgroup.inv_mem _ hkN) y).mp hy
        simpa using h
      refine ⟨k⁻¹ * y * k, hky, ?_⟩
      rw [map_mul, map_mul, map_inv, hyf]
      group
  -- The blue-print input at the conjugated pair.
  obtain ⟨_, S', hS'2, hS'FH, _, hS'N, hS'D, hS'sup⟩ :=
    hP3 G hS H hH t ht htH (X.map φ) (Y.map φ) hX'V hY'ne hsub' ⟨φ k, hk'K, hk'ne, hk'N⟩
  -- `S' ≤ C_G(X')`: `S' ≤ F ⊓ H` with `F = O^{2'}(C_G(X')) ≤ C_G(X')`.
  have hS'C : S' ≤ Subgroup.centralizer (X.map φ : Set G) := by
    refine (le_inf_iff.mp hS'FH).1.trans ?_
    calc (Submission.Blueprint.oddResidual (Subgroup.centralizer (X.map φ : Set G))).map
            (Subgroup.centralizer (X.map φ : Set G)).subtype
        ≤ (⊤ : Subgroup ↥(Subgroup.centralizer (X.map φ : Set G))).map
            (Subgroup.centralizer (X.map φ : Set G)).subtype := Subgroup.map_mono le_top
      _ = Subgroup.centralizer (X.map φ : Set G) := by
          rw [Subgroup.map_top, Subgroup.range_subtype]
  -- Transport lemmas for the conjugate of the structures of `X'` and `S'`.
  have hN'ψ : (Subgroup.normalizer (X.map φ : Set G)).map ψ =
      Subgroup.normalizer (X : Set G) := by
    rw [map_normalizer_of_bijective ⟨hψinj, hψsurj⟩, hXmap]
  have hC'ψ : (Subgroup.centralizer (X.map φ : Set G)).map ψ =
      Subgroup.centralizer (X : Set G) := by
    rw [map_centralizer_of_bijective ⟨hψinj, hψsurj⟩, hXmap]
  have hS'Nψ : (Subgroup.normalizer (S' : Set G)).map ψ =
      Subgroup.normalizer (S'.map ψ : Set G) :=
    map_normalizer_of_bijective ⟨hψinj, hψsurj⟩ S'
  refine ⟨S'.map ψ, hS'2.map ψ, ?_, ?_, ?_, ?_⟩
  · -- `S ≤ H ⊓ C_G(X)`
    refine le_inf ?_ ?_
    · calc S'.map ψ ≤ H.map ψ := Subgroup.map_mono ((le_inf_iff.mp hS'FH).2)
        _ = H := hHmap
    · calc S'.map ψ ≤ (Subgroup.centralizer (X.map φ : Set G)).map ψ := Subgroup.map_mono hS'C
        _ = Subgroup.centralizer (X : Set G) := hC'ψ
  · -- `S ⊓ D = ⊥`
    rw [← hDmap, ← Subgroup.map_inf S' (twoPoint H t) ψ hψinj, hS'D, Subgroup.map_bot]
  · -- `N_G(X) ⊓ H ≤ N_G(S)`
    have hmap := Subgroup.map_mono hS'N (f := ψ)
    rw [Subgroup.map_inf H _ ψ hψinj, hHmap, hN'ψ, hS'Nψ] at hmap
    rwa [inf_comm] at hmap
  · -- `H ⊓ N_G(X) = S ⊔ (D ⊓ N_G(X))`
    have hmap := congrArg (fun A : Subgroup G => A.map ψ) hS'sup
    rw [Subgroup.map_inf H _ ψ hψinj, hHmap, hN'ψ, Subgroup.map_sup,
        Subgroup.map_inf (twoPoint H t) _ ψ hψinj, hDmap, hN'ψ] at hmap
    exact hmap.symm

end Work.NormalComplement
