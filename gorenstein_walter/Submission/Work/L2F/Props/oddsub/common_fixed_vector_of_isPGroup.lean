import Mathlib

/-!
# A finite `p`-subgroup of `SL(2,F)` in characteristic `p` has a common fixed vector

Let `F` be a field of characteristic `p` and let `A ≤ SL(2,F)` be a finite `p`-group.  Then `A`
fixes a nonzero vector of `F²`.

The proof is the classical one.  A nontrivial finite `p`-group has a nontrivial centre; pick a
central element `z ≠ 1` and let `Z` be its matrix.  Because `z` has `p`-power order and
`X ^ (p ^ n) - 1 = (X - 1) ^ (p ^ n)` in characteristic `p`, the matrix `Z - 1` is nilpotent,
so its kernel `W = ker (Z - 1)` is nonzero.  As `z` is central, `W` is `A`-invariant, and since
`Z ≠ 1` acts on the `2`-dimensional space `F²`, `W` is exactly a line.  Every element of `A`
therefore acts on `W` by a scalar; that scalar has `p`-power order, and the only `p`-power root
of unity in characteristic `p` is `1`.  Hence `A` fixes `W` pointwise.

Main result: `Work.L2F.Props.oddsub.common_fixed_vector_of_isPGroup`.
-/

open Matrix

namespace Work.L2F.Props.oddsub

/-- In characteristic `p`, the only element of `F` whose `p`-th iterated power is `1` is `1`. -/
theorem eq_one_of_pow_pow_eq_one_aux (F : Type*) [Field F] (p : ℕ) [Fact p.Prime]
    (hp : CharP F p) (x : F) (n : ℕ) (h : x ^ p ^ n = 1) : x = 1 := by
  haveI := hp
  have hpn : p ^ n ≠ 0 := pow_ne_zero n (Nat.Prime.ne_zero Fact.out)
  have h2 : (x - 1) ^ (p ^ n) = 0 := by
    rw [sub_pow_char_pow x 1 n, h, one_pow, sub_self]
  exact sub_eq_zero.mp ((pow_eq_zero_iff hpn).mp h2)

/-- If `(M - 1) ^ m = 0` for some `m ≠ 0` then the `2 × 2` matrix `M` has a nonzero fixed
vector. -/
theorem exists_fixed_vector_of_sub_pow_eq_zero_aux (F : Type*) [Field F]
    (M : Matrix (Fin 2) (Fin 2) F) (m : ℕ) (hm : m ≠ 0) (h : (M - 1) ^ m = 0) :
    ∃ v : Fin 2 → F, v ≠ 0 ∧ M *ᵥ v = v := by
  have hdet : (M - 1).det = 0 := by
    have h1 : ((M - 1) ^ m).det = 0 := by rw [h]; simp
    rw [Matrix.det_pow] at h1
    exact (pow_eq_zero_iff hm).mp h1
  obtain ⟨v, hv, hMv⟩ := Matrix.exists_mulVec_eq_zero_iff.mpr hdet
  refine ⟨v, hv, ?_⟩
  have h2 := hMv
  rw [Matrix.sub_mulVec, Matrix.one_mulVec, sub_eq_zero] at h2
  exact h2

/-- A finite `p`-group acting faithfully on `F²` through `2 × 2` matrices over a field `F` of
characteristic `p` has a nonzero common fixed vector. -/
theorem exists_fixed_vector_of_isPGroup_of_injective_hom (F : Type*) [Field F] (p : ℕ)
    [Fact p.Prime] (hp : CharP F p) (G : Type*) [Group G] [Finite G] [Nontrivial G]
    (hG : IsPGroup p G) (ρ : G →* Matrix (Fin 2) (Fin 2) F) (hinj : Function.Injective ρ) :
    ∃ v : Fin 2 → F, v ≠ 0 ∧ ∀ g : G, ρ g *ᵥ v = v := by
  haveI : CharP F p := hp
  haveI : Nontrivial ↥(Subgroup.center G) := hG.center_nontrivial
  obtain ⟨z, hz⟩ := exists_ne (1 : ↥(Subgroup.center G))
  have hcent : (z : G) ∈ Subgroup.center G := z.2
  have hz1 : (z : G) ≠ 1 := fun h => hz (Subtype.ext h)
  obtain ⟨k, hk⟩ := hG.exists_pow_pow_eq_one (z : G)
  set Z : Matrix (Fin 2) (Fin 2) F := ρ (z : G) with hZdef
  have hZne : Z ≠ 1 := by
    rw [hZdef]
    intro h
    exact hz1 (hinj (by rw [h, map_one ρ]))
  have hZpow : Z ^ (p ^ k) = 1 := by
    have h := map_pow ρ (z : G) (p ^ k)
    rw [hk, map_one ρ] at h
    rw [hZdef]
    exact h.symm
  have hsub : (Z - 1) ^ (p ^ k) = 0 := by
    rw [sub_pow_char_pow_of_commute p k (Commute.one_right Z), hZpow, one_pow, sub_self]
  have hpn : p ^ k ≠ 0 := pow_ne_zero k (Nat.Prime.ne_zero Fact.out)
  obtain ⟨w, hw, hZw⟩ := exists_fixed_vector_of_sub_pow_eq_zero_aux F Z (p ^ k) hpn hsub
  have hwker : w ∈ (Matrix.toLin' (Z - 1)).ker := by
    rw [LinearMap.mem_ker, Matrix.toLin'_apply, Matrix.sub_mulVec, Matrix.one_mulVec,
      hZw, sub_self]
  have hne0 : Matrix.toLin' (Z - 1) ≠ 0 := by
    intro h0
    refine hZne (sub_eq_zero.mp (Matrix.toLin'.injective ?_))
    rw [h0, map_zero]
  have hspan_le : Submodule.span F {w} ≤ (Matrix.toLin' (Z - 1)).ker := by
    rw [Submodule.span_le, Set.singleton_subset_iff]
    exact hwker
  have hrange_ne : (Matrix.toLin' (Z - 1)).range ≠ ⊥ :=
    fun hbot => hne0 ((LinearMap.range_eq_bot).mp hbot)
  have hle1 : Module.finrank F ↥(Matrix.toLin' (Z - 1)).ker ≤ 1 := by
    have hsum := LinearMap.finrank_range_add_finrank_ker (Matrix.toLin' (Z - 1))
    have hV : Module.finrank F (Fin 2 → F) = 2 := Module.finrank_fin_fun F
    rw [hV] at hsum
    have h2 : 1 ≤ Module.finrank F ↥(Matrix.toLin' (Z - 1)).range := by
      have hnt : Nontrivial ↥(Matrix.toLin' (Z - 1)).range :=
        Submodule.nontrivial_iff_ne_bot.mpr hrange_ne
      have hpos : 0 < Module.finrank F ↥(Matrix.toLin' (Z - 1)).range :=
        Module.finrank_pos_iff.mpr hnt
      omega
    omega
  have hge1 : 1 ≤ Module.finrank F ↥(Matrix.toLin' (Z - 1)).ker := by
    have h := Submodule.finrank_mono hspan_le
    rwa [finrank_span_singleton hw] at h
  have hfin : Module.finrank F ↥(Matrix.toLin' (Z - 1)).ker = 1 := le_antisymm hle1 hge1
  have hspan : (Matrix.toLin' (Z - 1)).ker = Submodule.span F {w} :=
    (Submodule.eq_of_le_of_finrank_le hspan_le (by rw [hfin, finrank_span_singleton hw])).symm
  refine ⟨w, hw, fun g => ?_⟩
  have hcomm : ρ g * Z = Z * ρ g := by
    rw [hZdef]
    simpa only [map_mul] using congrArg ρ (Subgroup.mem_center_iff.mp hcent g)
  have hmem : ρ g *ᵥ w ∈ (Matrix.toLin' (Z - 1)).ker := by
    rw [LinearMap.mem_ker, Matrix.toLin'_apply, Matrix.sub_mulVec, Matrix.one_mulVec]
    have h1 : Z *ᵥ (ρ g *ᵥ w) = ρ g *ᵥ w := by
      rw [Matrix.mulVec_mulVec, ← hcomm, ← Matrix.mulVec_mulVec, hZw]
    rw [h1, sub_self]
  have hmem' : ρ g *ᵥ w ∈ Submodule.span F {w} := hspan ▸ hmem
  obtain ⟨c, hc⟩ := Submodule.mem_span_singleton.mp hmem'
  obtain ⟨n, hn⟩ := hG.exists_pow_pow_eq_one g
  have hc1 : c = 1 := by
    have hpowv : ∀ j : ℕ, (ρ g) ^ j *ᵥ w = c ^ j • w := by
      intro j
      induction j with
      | zero => simp [Matrix.one_mulVec]
      | succ i ih =>
        rw [pow_succ, ← Matrix.mulVec_mulVec, ← hc, Matrix.mulVec_smul, ih, smul_smul,
          ← pow_succ']
    have hgn : (ρ g) ^ (p ^ n) = 1 := by
      have h := map_pow ρ g (p ^ n)
      rw [hn, map_one ρ] at h
      exact h.symm
    have hwx : c ^ (p ^ n) • w = w := by
      rw [← hpowv (p ^ n), hgn, Matrix.one_mulVec]
    have h1 : c ^ (p ^ n) = 1 := by
      have h2 : (c ^ (p ^ n) - 1) • w = 0 := by
        rw [sub_smul, one_smul, hwx, sub_self]
      exact sub_eq_zero.mp ((smul_eq_zero.mp h2).resolve_right hw)
    exact eq_one_of_pow_pow_eq_one_aux F p hp c n h1
  rw [← hc, hc1, one_smul]

theorem common_fixed_vector_of_isPGroup (F : Type*) [Field F] (p : ℕ) [Fact p.Prime]
    (hp : CharP F p) (A : Subgroup (Matrix.SpecialLinearGroup (Fin 2) F))
    [Finite ↥A] (hA : IsPGroup p ↥A) (hne : A ≠ ⊥) :
    ∃ v : Fin 2 → F, v ≠ 0 ∧ ∀ a ∈ A,
      Matrix.mulVec ((a : Matrix.SpecialLinearGroup (Fin 2) F) : Matrix (Fin 2) (Fin 2) F) v = v := by
  haveI : Nontrivial ↥A := (Subgroup.nontrivial_iff_ne_bot A).mpr hne
  let ρ : ↥A →* Matrix (Fin 2) (Fin 2) F :=
    { toFun := fun a => ((a : Matrix.SpecialLinearGroup (Fin 2) F) : Matrix (Fin 2) (Fin 2) F)
      map_one' := rfl
      map_mul' := fun a b => rfl }
  have hinj : Function.Injective ρ := by
    intro a b hab
    exact Subtype.ext (Subtype.ext hab)
  obtain ⟨v, hv, hfix⟩ :=
    exists_fixed_vector_of_isPGroup_of_injective_hom F p hp ↥A hA ρ hinj
  exact ⟨v, hv, fun a ha => hfix ⟨a, ha⟩⟩

end Work.L2F.Props.oddsub
