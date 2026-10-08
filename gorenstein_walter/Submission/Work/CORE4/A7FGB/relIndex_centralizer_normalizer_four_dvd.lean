import Mathlib

/-!
# The index of `R ⊓ C_G(V)` in `R ⊓ N_G(V)` divides `6` when `V` has order `4`

Let `V` be a subgroup of a group `G` with exactly four elements.  An automorphism of `V`
permutes the three non-identity elements of `V`, and an automorphism fixing every
non-identity element is the identity (both fix `1`).  Hence `MulAut V` is isomorphic to a
subgroup of the symmetric group on three letters, and Lagrange's theorem gives
`Nat.card (MulAut V) ∣ 3! = 6`.

The conjugation action of the normalizer `N_G(V)` on `V` is a homomorphism with kernel
`C_G(V)`.  Restricting it along the inclusion `R ⊓ N_G(V) ≤ N_G(V)` yields a homomorphism
whose kernel is `R ⊓ C_G(V)`; consequently the relative index of `R ⊓ C_G(V)` in
`R ⊓ N_G(V)` is the order of a subgroup of `MulAut V`, and therefore divides `6`.
-/

namespace Work.CORE4.A7FGB

/-- An automorphism of a group with four elements is determined by its values on the three
non-identity elements, so the automorphism group has order dividing `3! = 6`. -/
lemma natCard_mulAut_dvd_six {H : Type*} [Group H] (hH : Nat.card H = 4) :
    Nat.card (MulAut H) ∣ 6 := by
  classical
  haveI : Finite H := (Nat.card_ne_zero.mp (by omega : Nat.card H ≠ 0)).2
  -- the three non-identity elements of `H`
  let S := {x : H // x ≠ 1}
  have hS : Nat.card S = 3 := by
    have h := Finite.card_option (α := S)
    rw [Nat.card_congr (Equiv.optionSubtypeNe (1 : H))] at h
    omega
  have hperm : Nat.card (Equiv.Perm S) = 6 := by rw [Nat.card_perm, hS]; norm_num
  -- restriction of an automorphism to the non-identity elements, as a monoid homomorphism
  let φ : MulAut H →* Equiv.Perm S :=
    { toFun := fun f =>
        Equiv.Perm.subtypePerm f.toEquiv (fun x => not_congr (MulEquiv.map_eq_one_iff f)),
      map_one' := by ext x; simp [Equiv.Perm.subtypePerm_apply]
      map_mul' := by intro f g; ext x; simp [Equiv.Perm.subtypePerm_apply] }
  have hφapp : ∀ (f : MulAut H) (x : H) (hx : x ≠ 1), (φ f ⟨x, hx⟩ : H) = f x := by
    intro f x hx
    change (↑(Equiv.Perm.subtypePerm (p := fun y : H => y ≠ 1) f.toEquiv
      (fun y => not_congr (MulEquiv.map_eq_one_iff f)) ⟨x, hx⟩) : H) = f x
    simp [Equiv.Perm.subtypePerm_apply]
  have hinj : Function.Injective φ := by
    intro f g hfg
    apply MulEquiv.ext
    intro x
    by_cases hx : x = 1
    · rw [hx]; simp
    · have h := congrArg (fun e : Equiv.Perm S => (e ⟨x, hx⟩ : H)) hfg
      rw [hφapp f x hx, hφapp g x hx] at h
      exact h
  calc Nat.card (MulAut H) ∣ Nat.card (Equiv.Perm S) :=
        Subgroup.card_dvd_of_injective φ hinj
    _ = 6 := hperm

theorem relIndex_centralizer_normalizer_four_dvd (R V : Subgroup (alternatingGroup (Fin 7)))
    (hVcard : Nat.card V = 4) (h2 : ∀ v ∈ V, v * v = 1) (hVR : V ≤ R) :
    (R ⊓ Subgroup.centralizer (V : Set (alternatingGroup (Fin 7)))).relIndex
      (R ⊓ Subgroup.normalizer (V : Set (alternatingGroup (Fin 7)))) ∣ 6 := by
  classical
  set N := Subgroup.normalizer (V : Set (alternatingGroup (Fin 7))) with hN
  set C := Subgroup.centralizer (V : Set (alternatingGroup (Fin 7))) with hC
  have hCN : C ≤ N := Subgroup.centralizer_le_normalizer _
  have hK : R ⊓ N ≤ N := inf_le_right
  -- the conjugation action of `R ⊓ N_G(V)` on `V`, through the normalizer of `V`
  let ψ : ↥(R ⊓ N) →* MulAut ↥V :=
    (Subgroup.normalizerMonoidHom V).comp (Subgroup.inclusion hK)
  -- its kernel is `R ⊓ C_G(V)`
  have hker : ψ.ker = (R ⊓ C).subgroupOf (R ⊓ N) := by
    have h1 : ψ.ker =
        Subgroup.comap (Subgroup.inclusion hK) (Subgroup.normalizerMonoidHom V).ker := by
      ext x
      simp [ψ, MonoidHom.mem_ker, Subgroup.mem_comap]
    have h2' : Subgroup.comap (Subgroup.inclusion hK) (Subgroup.normalizerMonoidHom V).ker
        = (R ⊓ C).subgroupOf (R ⊓ N) := by
      rw [Subgroup.normalizerMonoidHom_ker, Subgroup.comap_inclusion_subgroupOf]
      have heq : R ⊓ C = C ⊓ (R ⊓ N) := by
        rw [inf_comm R C, ← inf_assoc, inf_eq_left.mpr (le_trans inf_le_left hCN)]
      rw [heq, Subgroup.inf_subgroupOf_right]
    exact h1.trans h2'
  calc (R ⊓ C).relIndex (R ⊓ N)
      = ((R ⊓ C).subgroupOf (R ⊓ N)).index := rfl
    _ = ψ.ker.index := by rw [hker]
    _ = Nat.card ψ.range := Subgroup.index_ker ψ
    _ ∣ Nat.card (MulAut ↥V) := Subgroup.card_subgroup_dvd_card ψ.range
    _ ∣ 6 := natCard_mulAut_dvd_six hVcard

end Work.CORE4.A7FGB
