import Mathlib.GroupTheory.PGroup
import Submission.Work.ProP.card_quotient_lt
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

namespace Work.ProP

universe u

/-- In a nontrivial finite `p`-group the centre contains an element of order exactly `p`.

The centre of a nontrivial finite `p`-group is nontrivial (`IsPGroup.center_nontrivial`), hence
has order `p ^ e` with `e > 0` (`IsPGroup.nontrivial_iff_card`), so `p` divides its order; Cauchy's
theorem (`exists_prime_orderOf_dvd_card'`) then provides an element of order `p`. -/
theorem exists_mem_center_pow_eq_one_ne_one {p : ℕ} [Fact p.Prime] {P : Type u} [Group P]
    [Finite P] (hP : IsPGroup p P) (hnt : Nontrivial P) :
    ∃ z ∈ Subgroup.center P, z ^ p = 1 ∧ z ≠ 1 := by
  have hcnt : Nontrivial ↥(Subgroup.center P) := hP.center_nontrivial
  obtain ⟨e, he0, hecard⟩ := (hP.to_subgroup (Subgroup.center P)).nontrivial_iff_card.mp hcnt
  have hpdvd : p ∣ Nat.card ↥(Subgroup.center P) := by
    rw [hecard]; exact dvd_pow_self p (ne_of_gt he0)
  obtain ⟨z, hzorder⟩ := exists_prime_orderOf_dvd_card' p hpdvd
  have hzorder' : orderOf (z : P) = p := (Subgroup.orderOf_coe z).trans hzorder
  obtain ⟨hzp, hzne⟩ := (orderOf_eq_prime_iff (x := (z : P)) (p := p)).mp hzorder'
  exact ⟨(z : P), z.2, hzp, hzne⟩

/-- The main induction: cofinality of the descending `p`-central series of the free group in the
finite quotients, by strong induction on the order of the target finite `p`-group. -/
private theorem exists_pCentralSeries_le_ker_aux (p : ℕ) [Fact p.Prime] (n m : ℕ) :
    ∀ (P : Type u) [Group P] [Finite P], Nat.card P = m → IsPGroup p P →
      ∀ (φ : FreeGroup (Fin n) →* P),
        ∃ ν, Work.Shrinking.pCentralSeries p (FreeGroup (Fin n)) ν ≤ φ.ker := by
  induction m using Nat.strong_induction_on with
  | h m ih =>
    intro P _ _ hcard hP φ
    by_cases hnt : Nontrivial P
    · have hntI : Nontrivial P := hnt
      -- a central element `z` of order `p`
      obtain ⟨z, hzc, hzp, hzne⟩ := exists_mem_center_pow_eq_one_ne_one hP hnt
      -- the subgroup `C = ⟨z⟩` it generates
      let C : Subgroup P := Subgroup.zpowers z
      have hCcenter : C ≤ Subgroup.center P := Subgroup.zpowers_le.mpr hzc
      have hCnormal : C.Normal := by
        refine Subgroup.Normal.mk fun a ha g => ?_
        have h1 : g * a = a * g := Subgroup.mem_center_iff.mp (hCcenter ha) g
        rw [h1]; simpa using ha
      have hCnormI : C.Normal := hCnormal
      have hCpow : ∀ c ∈ C, c ^ p = 1 := by
        intro c hc
        obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp hc
        rw [← hk, ← zpow_natCast, ← zpow_mul z k, mul_comm, zpow_mul z (↑p), zpow_natCast,
          hzp, one_zpow]
      have hCne : C ≠ ⊥ := by
        intro h
        exact hzne (Subgroup.zpowers_eq_bot.mp h)
      -- the induction hypothesis, applied to the quotient by `C`
      have hcardlt : Nat.card (P ⧸ C) < Nat.card P := card_quotient_lt C hCne
      have hQ : IsPGroup p (P ⧸ C) :=
        hP.of_surjective (QuotientGroup.mk' C) (QuotientGroup.mk'_surjective C)
      obtain ⟨ν, hν⟩ :=
        ih (Nat.card (P ⧸ C)) (by rw [← hcard]; exact hcardlt) (P ⧸ C) rfl hQ
          ((QuotientGroup.mk' C).comp φ)
      refine ⟨ν + 1, ?_⟩
      -- `φ` maps `P_ν` into `C`
      have hmap : (Work.Shrinking.pCentralSeries p (FreeGroup (Fin n)) ν).map φ ≤ C := by
        rw [← QuotientGroup.ker_mk' C, Subgroup.map_le_iff_le_comap]
        intro x hx
        exact hν hx
      rw [Work.Shrinking.pCentralSeries_succ, Work.Shrinking.pCentralStep]
      refine sup_le ?_ ?_
      · -- the `p`-th powers of `P_ν` die: `(φ x)^p = 1` for `φ x ∈ C`
        rw [Work.Shrinking.powSubgroup, Subgroup.closure_le]
        rintro x ⟨y, hy, rfl⟩
        exact MonoidHom.mem_ker.mpr
          (by rw [map_pow]; exact hCpow (φ y) (hmap (Subgroup.mem_map.mpr ⟨y, hy, rfl⟩)))
      · -- the commutators `[P_ν, F]` die: `C` is central
        have hcommC : ⁅C, (⊤ : Subgroup P)⁆ = ⊥ :=
          Subgroup.commutator_top_right_eq_bot_iff_le_center.mpr hCcenter
        have h2 : (⁅Work.Shrinking.pCentralSeries p (FreeGroup (Fin n)) ν,
            ⊤⁆ : Subgroup (FreeGroup (Fin n))).map φ ≤ ⊥ := by
          rw [Subgroup.map_commutator]
          exact le_trans (Subgroup.commutator_mono hmap le_top) (le_of_eq hcommC)
        exact Subgroup.map_le_iff_le_comap.mp h2
    · -- `P` is trivial: take `ν = 0`
      have hsub : Subsingleton P := not_nontrivial_iff_subsingleton.mp hnt
      refine ⟨0, ?_⟩
      rw [Work.Shrinking.pCentralSeries_zero]
      intro x _
      exact MonoidHom.mem_ker.mpr (Subsingleton.elim _ _)

/-- **The generic kernel statement.**  Every homomorphism from the free group on `n` generators
to a finite `p`-group kills some term of the descending `p`-central filtration (cofinality of the
filtration in the profinite topology).

Proof (induction on `Nat.card P`, avoiding all Frattini theory):
* if `P` is trivial, `ν = 0` works (`FreeGroup (Fin n) ⧸ ⊤` is trivial);
* otherwise `Subgroup.center P` is nontrivial, so it contains a subgroup `C` of order `p`
  (`IsPGroup.bot_lt_center`, `IsPGroup.exists_orderOf_eq_pow`: raise an element of the centre of
  order `p ^ e`, `e ≥ 1`, to the `p ^ (e-1)`-st power).  Apply the induction hypothesis to the
  composite `FreeGroup (Fin n) →* P →* P ⧸ C`: there is `ν` with
  `pCentralSeries p (FreeGroup (Fin n)) ν ≤ (P ⧸ C ← φ).ker`, i.e.
  `φ (pCentralSeries p (FreeGroup (Fin n)) ν) ≤ C`.  Then
  `φ (pCentralSeries p (FreeGroup (Fin n)) (ν+1))
    ≤ φ(P_ν)^p ⁅φ(P_ν), P⁆ ≤ C^p ⁅C, P⁆ = ⊥`,
  because `C` is central of order `p`; so `pCentralSeries p (FreeGroup (Fin n)) (ν + 1) ≤ ker φ`.
The image computation uses `Work.Shrinking.map_pCentralSeries_surjective` (the filtration of a
quotient is the image of the filtration). -/
theorem exists_pCentralSeries_le_ker {p : ℕ} [Fact p.Prime] (n : ℕ) {P : Type*} [Group P]
    [Finite P] (hP : IsPGroup p P) (φ : FreeGroup (Fin n) →* P) :
    ∃ ν, Work.Shrinking.pCentralSeries p (FreeGroup (Fin n)) ν ≤ φ.ker :=
  exists_pCentralSeries_le_ker_aux p n (Nat.card P) P rfl hP φ

end Work.ProP
