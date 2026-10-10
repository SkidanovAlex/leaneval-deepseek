import Mathlib.Algebra.Lie.Free
import Submission.Work.SSGRoute.prop5.witt.Swap
import Submission.Work.SSGRoute.prop5.witt.Vocab
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

set_option maxHeartbeats 4000000

namespace Work.SSGRoute.prop5

open scoped commutatorElement

attribute [local instance 100] LieRing.ofAssociativeRing

noncomputable section

variable {X : Type} [LinearOrder X]

/-- The canonical Lie homomorphism from the free Lie ring on `X` to the free associative ring,
the latter regarded as a Lie ring through the commutator. -/
noncomputable def fL (X : Type) : FreeLieAlgebra ℤ X →ₗ⁅ℤ⁆ FreeAlgebra ℤ X :=
  FreeLieAlgebra.lift ℤ (fun x => (FreeAlgebra.ι ℤ x : FreeAlgebra ℤ X))

theorem fL_monLie (w : Magma X) : fL X (monLie X w) = monBrkA X w := by
  induction w with
  | gen x => exact FreeLieAlgebra.lift_of_apply (fun x => (FreeAlgebra.ι ℤ x : FreeAlgebra ℤ X)) x
  | mul a b iha ihb =>
      rw [monLie_mul, LieHom.map_lie, monBrkA_mul, iha, ihb, LieRing.of_associative_ring_bracket]

/-- The `ℤ`-span of the Lie evaluations of the Hall trees. -/
noncomputable def Sp (X : Type) [LinearOrder X] : Submodule ℤ (FreeLieAlgebra ℤ X) :=
  Submodule.span ℤ (Set.range (fun h : {h : Magma X // IsHall h} => monLie X h.1))

theorem Sp_lie_mem (hspan : ∀ w : Magma X, monLie X w ∈ Sp X) {x y : FreeLieAlgebra ℤ X}
    (hx : x ∈ Sp X) (hy : y ∈ Sp X) : ⁅x, y⁆ ∈ Sp X := by
  refine Submodule.span_induction (p := fun z _ => ∀ y ∈ Sp X, ⁅z, y⁆ ∈ Sp X) ?_ ?_ ?_ ?_ hx y hy
  · intro z hz y hy
    rcases hz with ⟨h, rfl⟩
    refine Submodule.span_induction (p := fun z _ => ⁅monLie X h.1, z⁆ ∈ Sp X) ?_ ?_ ?_ ?_ hy
    · intro z hz
      rcases hz with ⟨g, rfl⟩
      have h1 : monLie X (Magma.mul h.1 g.1) ∈ Sp X := hspan _
      rwa [monLie_mul] at h1
    · simp
    · intro a b _ _ ha hb; rw [lie_add]; exact Submodule.add_mem _ ha hb
    · intro c a _ ha; rw [lie_smul]; exact Submodule.smul_mem _ c ha
  · intro y hy; simp
  · intro a b _ _ ha hb y hy; rw [add_lie]; exact Submodule.add_mem _ (ha y hy) (hb y hy)
  · intro c a _ ha y hy; rw [smul_lie]; exact Submodule.smul_mem _ c (ha y hy)

theorem Sp_eq_top (hspan : ∀ w : Magma X, monLie X w ∈ Sp X) : Sp X = ⊤ := by
  let S' : LieSubalgebra ℤ (FreeLieAlgebra ℤ X) :=
    LieSubalgebra.mk (Sp X) (fun hx hy => Sp_lie_mem hspan hx hy)
  have hmem : ∀ x : X, FreeLieAlgebra.of ℤ x ∈ S' := by
    intro x
    exact hspan (Magma.gen x)
  let Ψ : FreeLieAlgebra ℤ X →ₗ⁅ℤ⁆ S' :=
    FreeLieAlgebra.lift ℤ (fun x => ⟨FreeLieAlgebra.of ℤ x, hmem x⟩)
  have hcomp : S'.incl.comp Ψ = LieHom.id := by
    apply FreeLieAlgebra.hom_ext
    intro x
    show S'.incl (Ψ (FreeLieAlgebra.of ℤ x)) = FreeLieAlgebra.of ℤ x
    have h1 : Ψ (FreeLieAlgebra.of ℤ x) = ⟨FreeLieAlgebra.of ℤ x, hmem x⟩ :=
      FreeLieAlgebra.lift_of_apply (fun y => (⟨FreeLieAlgebra.of ℤ y, hmem y⟩ : S')) x
    rw [h1]
    rfl
  have htop : ∀ z : FreeLieAlgebra ℤ X, z ∈ S'.toSubmodule := by
    intro z
    have hz : S'.incl (Ψ z) = z := by
      have h2 := congr_arg (fun (φ : FreeLieAlgebra ℤ X →ₗ⁅ℤ⁆ FreeLieAlgebra ℤ X) => φ z) hcomp
      simpa using h2
    rw [← hz]
    exact (Ψ z).2
  ext z
  simp only [Submodule.mem_top, iff_true]
  exact htop z

end

section Coeff

variable {X : Type} [LinearOrder X]

/-- The coefficient of a word in `monBrkA X w` agrees with the corresponding coefficient of
`monBrk X w`. -/
theorem coeffF_zero (u : List X) : coeffF (0 : MonoidAlgebra ℤ (FreeMonoid X)) u = 0 := by
  simp [coeffF]

theorem coeffF_equivA (w : Magma X) (u : List X) :
    coeffF (monBrk X w) u
      = coeffF (FreeAlgebra.equivMonoidAlgebraFreeMonoid (monBrkA X w)) u :=
  (congrArg (fun a => coeffF a u) (equivMonoidAlgebra_monBrkA w)).symm

theorem coeffF_smul (c : ℤ) (a : MonoidAlgebra ℤ (FreeMonoid X)) (u : List X) :
    coeffF (c • a) u = c * coeffF a u := by
  simp only [coeffF]
  rw [MonoidAlgebra.coeff_smul_apply, smul_eq_mul]

theorem coeffF_sum {ι : Type*} (s : Finset ι) (f : ι → MonoidAlgebra ℤ (FreeMonoid X))
    (u : List X) :
    coeffF (∑ i ∈ s, f i) u = ∑ i ∈ s, coeffF (f i) u := by
  classical
  induction s using Finset.induction with
  | empty => simp [coeffF]
  | insert a s ha ih => simp [Finset.sum_insert ha, coeffF_add, ih]

end Coeff

section Main

variable {X : Type} [LinearOrder X]

/-- The `monLie` images of distinct Hall trees are distinct in the free Lie algebra, as a
consequence of the leading-term description of the bracket evaluation. -/
theorem monLie_inj_of_coeff
    (hlead : ∀ c : Magma X, IsHall c →
      coeffF (monBrk X c) (Magma.foliage c) = 1 ∧
        ∀ w : List X, w < Magma.foliage c → coeffF (monBrk X c) w = 0)
    (hinj : ∀ a b : Magma X, IsHall a → IsHall b → Magma.foliage a = Magma.foliage b → a = b)
    {a b : Magma X} (ha : IsHall a) (hb : IsHall b) (h : monLie X a = monLie X b) : a = b := by
  by_cases hfab : Magma.foliage a = Magma.foliage b
  · exact hinj a b ha hb hfab
  · exfalso
    have hbrk : monBrkA X a = monBrkA X b := by
      have := congrArg (fL X) h
      rwa [fL_monLie, fL_monLie] at this
    rcases lt_or_gt_of_ne hfab with hlt | hgt
    · have hcoeff : coeffF (monBrk X a) (Magma.foliage a) = coeffF (monBrk X b) (Magma.foliage a) := by
        rw [coeffF_equivA a, coeffF_equivA b, hbrk]
      rw [(hlead a ha).1, (hlead b hb).2 _ hlt] at hcoeff
      exact one_ne_zero hcoeff
    · have hcoeff : coeffF (monBrk X a) (Magma.foliage b) = coeffF (monBrk X b) (Magma.foliage b) := by
        rw [coeffF_equivA a, coeffF_equivA b, hbrk]
      rw [(hlead b hb).1, (hlead a ha).2 _ hgt] at hcoeff
      exact one_ne_zero hcoeff.symm

/-- **Independence of the bracket evaluations of the Hall trees.** -/
theorem independence
    (hlead : ∀ c : Magma X, IsHall c →
      coeffF (monBrk X c) (Magma.foliage c) = 1 ∧
        ∀ w : List X, w < Magma.foliage c → coeffF (monBrk X c) w = 0)
    (hinj : ∀ a b : Magma X, IsHall a → IsHall b → Magma.foliage a = Magma.foliage b → a = b)
    (s : Finset {h : Magma X // IsHall h}) (α : {h : Magma X // IsHall h} → ℤ)
    (hzero : (∑ h ∈ s, α h • monBrkA X h.1) = 0) :
    ∀ h ∈ s, α h = 0 := by
  classical
  by_contra hcon
  push_neg at hcon
  obtain ⟨h₁, h₁s, h₁ne⟩ := hcon
  set s' := s.filter (fun h => α h ≠ 0) with hs'
  have hs'ne : s'.Nonempty := ⟨h₁, by simp [hs', h₁s, h₁ne]⟩
  obtain ⟨h₀, h₀s', h₀min⟩ := Finset.exists_min_image s' (fun h => Magma.foliage h.1) hs'ne
  rw [hs', Finset.mem_filter] at h₀s'
  obtain ⟨h₀s, h₀ne⟩ := h₀s'
  -- transport the relation to the monoid algebra
  have hzero' : (∑ h ∈ s, α h • monBrk X h.1) = 0 := by
    have h2 := congrArg (FreeAlgebra.equivMonoidAlgebraFreeMonoid) hzero
    simpa [map_sum, equivMonoidAlgebra_monBrkA] using h2
  -- the coefficient of the minimal foliage
  have hkey : coeffF (∑ h ∈ s, α h • monBrk X h.1) (Magma.foliage h₀.1) = α h₀ := by
    rw [coeffF_sum, Finset.sum_eq_single h₀]
    · rw [coeffF_smul, (hlead h₀.1 h₀.2).1, mul_one]
    · intro h hs hne
      rw [coeffF_smul]
      by_cases hα : α h = 0
      · rw [hα, zero_mul]
      · have hh : h ∈ s' := by simp [hs', hs, hα]
        have hle := h₀min h hh
        rcases lt_or_eq_of_le hle with hlt | heq
        · rw [(hlead h.1 h.2).2 _ hlt, mul_zero]
        · exact absurd (Subtype.ext (hinj h₀.1 h.1 h₀.2 h.2 heq)).symm hne
    · intro h₀not; exact absurd h₀s h₀not
  rw [hzero', coeffF_zero] at hkey
  exact h₀ne hkey.symm

/-- Independence, in the finitely-supported-index form. -/
theorem independence_finsupp
    (hlead : ∀ c : Magma X, IsHall c →
      coeffF (monBrk X c) (Magma.foliage c) = 1 ∧
        ∀ w : List X, w < Magma.foliage c → coeffF (monBrk X c) w = 0)
    (hinj : ∀ a b : Magma X, IsHall a → IsHall b → Magma.foliage a = Magma.foliage b → a = b)
    (c : {h : Magma X // IsHall h} →₀ ℤ)
    (h : c.sum (fun h r => r • monBrkA X h.1) = 0) : c = 0 := by
  classical
  rw [Finsupp.ext_iff]
  intro h₀
  have hsum : (∑ h ∈ c.support, c h • monBrkA X h.1) = 0 := by
    rw [← Finsupp.sum_of_support_subset c (Finset.Subset.refl _)
      (fun h r => r • monBrkA X h.1) (by simp)]
    exact h
  have := independence hlead hinj c.support (fun h => c h) hsum
  by_cases hh : h₀ ∈ c.support
  · simpa using this h₀ hh
  · simpa [Finsupp.mem_support_iff] using hh

/-- **The main theorem, in the ordered case.** -/
theorem fL_injective
    (hspan : ∀ w : Magma X, monLie X w ∈ Sp X)
    (hlead : ∀ c : Magma X, IsHall c →
      coeffF (monBrk X c) (Magma.foliage c) = 1 ∧
        ∀ w : List X, w < Magma.foliage c → coeffF (monBrk X c) w = 0)
    (hinj : ∀ a b : Magma X, IsHall a → IsHall b → Magma.foliage a = Magma.foliage b → a = b)
    {z w : FreeLieAlgebra ℤ X} (hzw : fL X z = fL X w) : z = w := by
  classical
  have htop : Sp X = ⊤ := Sp_eq_top hspan
  have hmem : z - w ∈ Sp X := by rw [htop]; exact Submodule.mem_top
  rw [Sp, Submodule.mem_span_set] at hmem
  obtain ⟨c, hcsub, hcsum⟩ := hmem
  have hex : ∀ x ∈ c.support, ∃ h : {h : Magma X // IsHall h}, monLie X h.1 = x :=
    fun x hx => by rcases hcsub hx with ⟨h, hh⟩; exact ⟨h, hh⟩
  set f : {h : Magma X // IsHall h} → FreeLieAlgebra ℤ X := fun h => monLie X h.1 with hf
  have hinjOn : Set.InjOn f (f ⁻¹' ↑c.support) := by
    intro a _ b _ hab
    exact Subtype.ext (monLie_inj_of_coeff hlead hinj a.2 b.2 hab)
  have hbij : Set.BijOn f (f ⁻¹' ↑c.support) ↑c.support := by
    refine ⟨fun h hh => hh, hinjOn, ?_⟩
    intro x hx
    rcases hex x hx with ⟨h, hh⟩
    have hmem : f h ∈ c.support := by
      rw [hf]
      show monLie X h.1 ∈ c.support
      rw [hh]
      exact hx
    exact ⟨h, hmem, by rw [hf]; exact hh⟩
  set c' : {h : Magma X // IsHall h} →₀ ℤ := Finsupp.comapDomain f c hbij.2.1 with hc'def
  have hsumL : c'.sum (fun h r => r • f h) = c.sum (fun x r => r • x) := by
    show (Finsupp.comapDomain f c hbij.2.1).sum (fun h r => r • f h) = c.sum (fun x r => r • x)
    exact Finsupp.sum_comapDomain f c (fun x r => r • x) hbij
  have hsumB : c'.sum (fun h r => r • monBrkA X h.1) = 0 := by
    have h1 : c'.sum (fun h r => r • monBrkA X h.1)
        = c'.sum (fun h r => r • fL X (f h)) := by
      refine Finsupp.sum_congr (fun h _ => ?_)
      rw [hf, fL_monLie]
    have h2 : c'.sum (fun h r => r • fL X (f h)) = fL X (c'.sum (fun h r => r • f h)) := by
      rw [Finsupp.sum_of_support_subset c' (Finset.Subset.refl _) (fun h r => r • fL X (f h))
        (by simp)]
      rw [Finsupp.sum_of_support_subset c' (Finset.Subset.refl _) (fun h r => r • f h) (by simp)]
      rw [map_sum]
      refine Finset.sum_congr rfl (fun h _ => ?_)
      rw [map_smul]
    rw [h1, h2, hsumL, hcsum, map_sub, hzw, sub_self]
  have hc' : c' = 0 := independence_finsupp hlead hinj c' hsumB
  have : z - w = 0 := by
    rw [← hcsum, ← hsumL, hc']
    simp
  exact sub_eq_zero.mp this

end Main

end Work.SSGRoute.prop5
