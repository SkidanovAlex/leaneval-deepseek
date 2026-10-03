import Mathlib
import Submission.Work.OROneRel.halfAtPrelude
import Submission.Work.OROneRel.mk_ne_one_of_misses_letter
import Submission.Work.OROneRel.substDefs
import Submission.Work.OROneRel.mmStepData_of_expsum_zero
import Submission.Work.OROneRel.rho_magnet
import Submission.Work.OROneRel.sigma_t_Psi
import Submission.Work.OROneRel.psiSubstDefs
import Submission.Work.OROneRel.nt_lt_relatorNorm
import Submission.Work.OROneRel.exists_two_mem_relatorLetters_ne
import Submission.Work.OROneRel.not_isProperPower_of_isConj
import Submission.Work.OROneRel.relatorNorm_magRewRel_letterCountNot
import Submission.Work.OROneRel.isProperPower_subst_iff_powSubst
import Submission.Work.OROneRel.powSubst_injective
import Submission.Work.OROneRel.wneSubstLocalisationB
import Submission.Work.OROneRel.wneDescentNoHzB
import Submission.Work.OROneRel.wneCounting
import Submission.Work.OROneRel.wnePsiNotProperPower
import Submission.Work.OROneRel.wneEpsSubst

namespace Work.OROneRel

universe u

/-! ## The no-zero-exponent-sum case of Weinbaum's theorem

`Work.OROneRel.weinbaum_half_noZero` is the case of Weinbaum's half-length statement in which no
letter of the cyclically reduced relator `T` has vanishing exponent sum, the half-length statement
being available for every relator of strictly smaller norm: `Work.OROneRel.HalfAt T`.

The counterexample `w` is a nontrivial half-length subword of a power of `T` which is trivial in
`⟨β | T⟩` (`PresentedGroup.mk {T} w = 1`).  The proof transports it to a strictly shorter relator, by
the following chain (all of whose inputs are separate modules of this directory):

1. `Work.OROneRel.wneCounting`: since `w` is a subword of `T ^ k` of length at most half of `T` and
   `T` has at least two letters, *some* letter `y` of `T` satisfies
   `letterCountNot y w < letterCountNot y T`.  Take such a `y`, and any letter `x ≠ y` of `T`.

2. `Work.OROneRel.wneSubstLocalisation`: the Magnus/Putman substitution
   `subst y x (σ_x T) (σ_y T)` (`t ↦ t ^ σ_x T`, `x ↦ x * t ^ (-σ_y T)`, all other letters fixed)
   makes the exponent sum in `y` vanish, and the *Magnus decoration* of the substituted arc is -- up
   to one overall shift of the decorations -- a subword `U` of a power of the Magnus rewriting
   `mmW y V` of a cyclically reduced conjugate `V` of the substituted relator, with
   `relatorNorm (mmW y V) = letterCountNot y T < relatorNorm T`.

3. `Work.OROneRel.wneEpsSubst` and `Work.OROneRel.wnePsiNotProperPower` supply the two structural
   facts about the substituted relator needed for the descent: the substituted arc has vanishing
   exponent sum in `y` (so that `rho` recovers it), and `V` is not a proper power (so that `mmW y V`
   is not one, by `not_isProperPower_mmW`).

4. `Work.OROneRel.wneDescentNoHzB` (the descent to the Magnus base) turns the triviality of the
   substituted arc in `⟨V⟩` into the triviality of `U` in the base `⟨mmW y V⟩`.

5. The induction hypothesis at `mmW y V` -- of norm `letterCountNot y T < relatorNorm T` -- together
   with the complementary-arc argument `Work.OROneRel.exists_complement_counterexample` then gives the
   contradiction: `U` is a nontrivial subword of a power of `mmW y V` which is trivial there. -/

/-- **The no-zero case, when the arc misses a letter of the relator.**  This is the elementary part of
the case: if the short subword `w` does not involve some letter `a` of `T`, then `w` lies in the
Magnus subgroup on the remaining generators while `T` does not, so the Freiheitssatz gives
`w ≠ 1` in `⟨β | T⟩`. -/
theorem halfAt_noZero_arc_misses_letter {β : Type u} (T : FreeGroup β)
    (hcyc : Work.OROneRel.IsCyclicallyReducedRelator T)
    (k : ℕ) (w : FreeGroup β) (hw1 : w ≠ 1)
    (hmiss : ∃ a ∈ Work.OROneRel.relatorLetters T, a ∉ Work.OROneRel.relatorLetters w) :
    PresentedGroup.mk ({T} : Set (FreeGroup β)) w ≠ 1 := by
  obtain ⟨a, ha, haw⟩ := hmiss
  exact Work.OROneRel.mk_ne_one_of_misses_letter hcyc ha haw hw1

/-! ## Glue for the substitution and the descent -/

/-- The substitution `subst t x p q` on the generator `t`. -/
theorem wne_subst_apply_of_t {α : Type u} (t x : α) (p q : ℤ) :
    Work.OROneRel.subst t x p q (FreeGroup.of t) = (FreeGroup.of t) ^ p := by
  rw [Work.OROneRel.subst, FreeGroup.lift_apply_of]
  simp [Work.OROneRel.substFun]

/-- The substitution `subst t x p q` on the generator `x`. -/
theorem wne_subst_apply_of_x {α : Type u} {t x : α} (hxt : x ≠ t) (p q : ℤ) :
    Work.OROneRel.subst t x p q (FreeGroup.of x) = FreeGroup.of x * (FreeGroup.of t) ^ (-q) := by
  rw [Work.OROneRel.subst, FreeGroup.lift_apply_of]
  simp [Work.OROneRel.substFun, hxt]

/-- The substitution `subst t x p q` fixes every other generator. -/
theorem wne_subst_apply_of_ne {α : Type u} {t x a : α} (hat : a ≠ t) (hax : a ≠ x) (p q : ℤ) :
    Work.OROneRel.subst t x p q (FreeGroup.of a) = FreeGroup.of a := by
  rw [Work.OROneRel.subst, FreeGroup.lift_apply_of]
  simp [Work.OROneRel.substFun, hat, hax]

/-- The Magnus/Putman substitution `Psi R y x` is the substitution `subst y x (σ_x R) (σ_y R)`. -/
theorem wne_Psi_eq_subst {α : Type u} (R : FreeGroup α) (y x : α) :
    Work.OROneRel.Psi R y x =
      Work.OROneRel.subst y x (Multiplicative.toAdd (Work.OROneRel.sigma x R))
        (Multiplicative.toAdd (Work.OROneRel.sigma y R)) := by
  apply FreeGroup.ext_hom
  intro a
  by_cases hay : a = y
  · subst hay
    rw [Work.OROneRel.Psi_of_eq_t, wne_subst_apply_of_t]
  · by_cases hax : a = x
    · subst hax
      rw [Work.OROneRel.Psi_of_eq_x hay, wne_subst_apply_of_x hay]
    · rw [Work.OROneRel.Psi_of_ne hay hax, wne_subst_apply_of_ne hay hax]

/-- A homomorphism maps the normal closure of `g` into the normal closure of its image. -/
theorem wne_normalClosure_le {G H : Type*} [Group G] [Group H] (ρ : G →* H) (g : G) :
    Subgroup.normalClosure ({g} : Set G) ≤ (Subgroup.normalClosure ({ρ g} : Set H)).comap ρ := by
  apply Subgroup.normalClosure_le_normal
  intro y hy
  rw [Set.mem_singleton_iff] at hy
  subst hy
  exact Subgroup.subset_normalClosure (by simp)

/-- The exponent sum is invariant under conjugation. -/
theorem wne_sigma_conj {α : Type u} (a : α) (c X : FreeGroup α) :
    Work.OROneRel.sigma a (c * X * c⁻¹) = Work.OROneRel.sigma a X := by
  rw [map_mul, map_mul, map_inv, mul_assoc,
    mul_comm (Work.OROneRel.sigma a X) ((Work.OROneRel.sigma a c)⁻¹),
    ← mul_assoc, mul_inv_cancel, one_mul]

/-- The substitution `subst y x p q` is injective for `p ≠ 0` and `x ≠ y`: it is the Nielsen
substitution `y ↦ y ^ p` followed by the automorphism `x ↦ x * y ^ (-q)`. -/
theorem wne_subst_injective {α : Type u} {y x : α} (hxy : x ≠ y) (p q : ℤ) (hp : p ≠ 0) :
    Function.Injective (Work.OROneRel.subst y x p q) := by
  intro a b hab
  rw [Work.OROneRel.ips_subst_comp_powSubst hxy p q] at hab
  simp only [MonoidHom.comp_apply] at hab
  have hh := Work.OROneRel.ips_subst_one_leftInverse (t := y) (x := x) hxy q
  have ha : Work.OROneRel.subst y x 1 (-q)
      (Work.OROneRel.subst y x 1 q (Work.OROneRel.powSubst y p a)) = Work.OROneRel.powSubst y p a :=
    DFunLike.congr_fun hh _
  have hb : Work.OROneRel.subst y x 1 (-q)
      (Work.OROneRel.subst y x 1 q (Work.OROneRel.powSubst y p b)) = Work.OROneRel.powSubst y p b :=
    DFunLike.congr_fun hh _
  rw [hab] at ha
  exact Work.OROneRel.powSubst_injective y p hp (ha.symm.trans hb)

/-! ## The case -/

/-- **Case 2 of Weinbaum's result: the no-zero-exponent-sum case.**  Given the half-length statement
for every relator of strictly smaller norm (over every generating type), it holds for a cyclically
reduced relator `T` which is not a proper power and in which *no* letter has exponent sum zero.

This is the deep case and the last input of `Work.OROneRel.weinbaum_sigma_zero_half`.

The counterexample `w` (a nontrivial half-length subword of a power of `T` which is trivial in
`⟨β | T⟩`) is transported to the strictly shorter relator `Work.OROneRel.mmW y V`, the Magnus base of
a cyclically reduced conjugate `V` of the Magnus/Putman substituted relator: the counting step
`wneCounting` picks a letter `y` for which the number of non-`y` letters strictly drops, the decorated
localisation `wneSubstLocalisation` decorates the substituted arc into a subword of a power of the
rewritten relator, the descent `wneDescentNoHzB` (with `wneEpsSubst` and
`wnePsiNotProperPower` supplying `rho`-recoverability and proper-power-freeness) turns its triviality
in `⟨V⟩` into triviality in the base `⟨mmW y V⟩`, and the induction hypothesis at the base -- of norm
`letterCountNot y T < relatorNorm T` -- together with the complementary arc
`Work.OROneRel.exists_complement_counterexample` gives the contradiction. -/
theorem weinbaum_half_noZero {β : Type u} (T : FreeGroup β)
    (IH : ∀ {γ : Type u} (U : FreeGroup γ), Work.OROneRel.relatorNorm U < Work.OROneRel.relatorNorm T →
      Work.OROneRel.IsCyclicallyReducedRelator U → ¬ Work.OROneRel.IsProperPower U →
      Work.OROneRel.HalfAt U)
    (hcyc : Work.OROneRel.IsCyclicallyReducedRelator T)
    (hpp : ¬ Work.OROneRel.IsProperPower T)
    (hσ : ∀ y ∈ Work.OROneRel.relatorLetters T, Work.OROneRel.expSum y T ≠ 1) :
    Work.OROneRel.HalfAt T := by
  classical
  intro k w hsub hhalf hw1 hcontra
  -- `w` is nontrivial, hence of length at least one
  have hwpos : 1 ≤ Work.OROneRel.relatorNorm w := by
    rcases Nat.eq_zero_or_pos (Work.OROneRel.relatorNorm w) with h | h
    · exfalso
      have h0 : FreeGroup.norm w = 0 := by simpa [Work.OROneRel.relatorNorm] using h
      exact hw1 (FreeGroup.norm_eq_zero.mp h0)
    · exact h
  have hrpos : 2 ≤ Work.OROneRel.relatorNorm T := by omega
  -- the counting step provides the localising letter `y`
  obtain ⟨y, hy, hylt⟩ := wneCounting T w hcyc hpp hrpos hsub hhalf hw1
  -- a second letter `x ≠ y` of `T`
  obtain ⟨x, hx, hxy⟩ : ∃ x ∈ Work.OROneRel.relatorLetters T, x ≠ y := by
    obtain ⟨x₀, hx₀, y₀, hy₀, hx₀y₀⟩ :=
      Work.OROneRel.exists_two_mem_relatorLetters_ne T hrpos hpp
    by_cases h : x₀ ≠ y
    · exact ⟨x₀, hx₀, h⟩
    · push_neg at h
      exact ⟨y₀, hy₀, fun hh => hx₀y₀ (by rw [h, hh])⟩
  -- the exponent sums are non-zero
  have hσy : Work.OROneRel.sigma y T ≠ 1 := hσ y hy
  have hσx : Work.OROneRel.sigma x T ≠ 1 := hσ x hx
  have hpy : Multiplicative.toAdd (Work.OROneRel.sigma y T) ≠ 0 := fun h0 =>
    hσy (Multiplicative.toAdd.injective (by rw [h0]; rfl))
  have hpx : Multiplicative.toAdd (Work.OROneRel.sigma x T) ≠ 0 := fun h0 =>
    hσx (Multiplicative.toAdd.injective (by rw [h0]; rfl))
  -- the substitution and its exponent sum in `y`
  have hPsi : Work.OROneRel.Psi T y x =
      Work.OROneRel.subst y x (Multiplicative.toAdd (Work.OROneRel.sigma x T))
        (Multiplicative.toAdd (Work.OROneRel.sigma y T)) := wne_Psi_eq_subst T y x
  have hwt : Work.OROneRel.sigma y (Work.OROneRel.subst y x
      (Multiplicative.toAdd (Work.OROneRel.sigma x T))
      (Multiplicative.toAdd (Work.OROneRel.sigma y T)) T) = 1 := by
    rw [← hPsi]
    exact Work.OROneRel.sigma_t_Psi T y x hxy
  -- the decorated localisation of the substituted arc
  obtain ⟨c, V, j, U, hVc, hVcyc, hsubU, hproj, hUlen, hMnorm⟩ :=
    wneSubstLocalisationB T (x := x) (t := y)
      (Multiplicative.toAdd (Work.OROneRel.sigma x T))
      (Multiplicative.toAdd (Work.OROneRel.sigma y T)) hcyc hxy hpx hpy hwt hsub
  -- `V` is not a proper power
  have hVpp : ¬ Work.OROneRel.IsProperPower V := by
    refine Work.OROneRel.not_isProperPower_of_isConj
      (X := V) (v := Work.OROneRel.Psi T y x T) ?_ ?_
    · rw [hPsi]
      exact wnePsiNotProperPower T (y := y) (x := x) hxy hcyc hpp hpx
    · exact isConj_iff.mpr ⟨c, hVc.symm⟩
  have hV1 : V ≠ 1 := Work.OROneRel.ne_one_of_not_isProperPower hVpp
  -- `V` has vanishing exponent sum in `y`
  have hσV : Work.OROneRel.sigma y V = 1 := by
    rw [hVc, wne_sigma_conj y c (Work.OROneRel.subst y x
      (Multiplicative.toAdd (Work.OROneRel.sigma x T))
      (Multiplicative.toAdd (Work.OROneRel.sigma y T)) T)]
    exact hwt
  have hεV : Work.OROneRel.eps y V = 0 :=
    (Work.OROneRel.eps_eq_zero_iff_sigma_eq_one y V).mpr hσV
  -- the substituted arc is nontrivial and has vanishing exponent sum in `y`
  have hsubst_w_ne : Work.OROneRel.subst y x (Multiplicative.toAdd (Work.OROneRel.sigma x T))
      (Multiplicative.toAdd (Work.OROneRel.sigma y T)) w ≠ 1 :=
    fun h1 => hw1 (wne_subst_injective hxy _ _ hpx h1)
  have hεw : Work.OROneRel.eps y (c * Work.OROneRel.subst y x
      (Multiplicative.toAdd (Work.OROneRel.sigma x T))
      (Multiplicative.toAdd (Work.OROneRel.sigma y T)) w * c⁻¹) = 0 := by
    rw [Work.OROneRel.eps_eq_zero_iff_sigma_eq_one, wne_sigma_conj]
    exact (Work.OROneRel.eps_eq_zero_iff_sigma_eq_one y _).mp
      (wneEpsSubst T (y := y) (x := x) hxy w hcontra)
  -- the substituted arc is trivial in `⟨V⟩`
  have hcontraV : PresentedGroup.mk ({V} : Set (FreeGroup β)) (c *
      Work.OROneRel.subst y x (Multiplicative.toAdd (Work.OROneRel.sigma x T))
      (Multiplicative.toAdd (Work.OROneRel.sigma y T)) w * c⁻¹) = 1 := by
    have hmem0 := Subgroup.mem_comap.mp (wne_normalClosure_le
      (Work.OROneRel.subst y x (Multiplicative.toAdd (Work.OROneRel.sigma x T))
        (Multiplicative.toAdd (Work.OROneRel.sigma y T))) T
      ((PresentedGroup.mk_eq_one_iff).mp hcontra))
    have hmem1 := Subgroup.mem_comap.mp (wne_normalClosure_le (MulAut.conj c).toMonoidHom
      (Work.OROneRel.subst y x (Multiplicative.toAdd (Work.OROneRel.sigma x T))
        (Multiplicative.toAdd (Work.OROneRel.sigma y T)) T) hmem0)
    have hmem2 : c * Work.OROneRel.subst y x (Multiplicative.toAdd (Work.OROneRel.sigma x T))
        (Multiplicative.toAdd (Work.OROneRel.sigma y T)) w * c⁻¹ ∈
        Subgroup.normalClosure ((singleton (c * Work.OROneRel.subst y x
          (Multiplicative.toAdd (Work.OROneRel.sigma x T))
          (Multiplicative.toAdd (Work.OROneRel.sigma y T)) T * c⁻¹)) : Set (FreeGroup β)) := by
      simpa [MulAut.conj_apply] using hmem1
    rw [hVc]
    exact (PresentedGroup.mk_eq_one_iff).mpr hmem2
  -- the descent to the Magnus base
  have hmkU : PresentedGroup.mk ({Work.OROneRel.mmW y V} :
      Set (FreeGroup (Work.OROneRel.mmBeta y V))) U = 1 :=
    wneDescentNoHzB (R := V) (z := y) (w := c * Work.OROneRel.subst y x
      (Multiplicative.toAdd (Work.OROneRel.sigma x T))
      (Multiplicative.toAdd (Work.OROneRel.sigma y T)) w * c⁻¹)
      hV1 hεV hVcyc hεw hcontraV j U hproj
  -- the transported counterexample is nontrivial
  have hU1 : U ≠ 1 := by
    intro hU0
    have hπ1 : FreeGroup.map (fun z : Work.OROneRel.mmBeta y V =>
        ((z.1.1, z.1.2) : ({t : β // t ≠ y} × ℤ))) U = 1 := by rw [hU0, map_one]
    rw [hproj] at hπ1
    have hmr1 : Work.OROneRel.magRewRel y (c * Work.OROneRel.subst y x
        (Multiplicative.toAdd (Work.OROneRel.sigma x T))
        (Multiplicative.toAdd (Work.OROneRel.sigma y T)) w * c⁻¹) = 1 :=
      (Work.OROneRel.magShiftAut y j).injective (by rwa [map_one])
    have h2 : c * Work.OROneRel.subst y x (Multiplicative.toAdd (Work.OROneRel.sigma x T))
        (Multiplicative.toAdd (Work.OROneRel.sigma y T)) w * c⁻¹ = 1 := by
      have hmr : Work.OROneRel.rho y (Work.OROneRel.magRewRel y (c * Work.OROneRel.subst y x
          (Multiplicative.toAdd (Work.OROneRel.sigma x T))
          (Multiplicative.toAdd (Work.OROneRel.sigma y T)) w * c⁻¹)) =
          c * Work.OROneRel.subst y x (Multiplicative.toAdd (Work.OROneRel.sigma x T))
          (Multiplicative.toAdd (Work.OROneRel.sigma y T)) w * c⁻¹ := by
        rw [show Work.OROneRel.magRewRel y (c * Work.OROneRel.subst y x
            (Multiplicative.toAdd (Work.OROneRel.sigma x T))
            (Multiplicative.toAdd (Work.OROneRel.sigma y T)) w * c⁻¹) =
            Work.OROneRel.magnet (c * Work.OROneRel.subst y x
            (Multiplicative.toAdd (Work.OROneRel.sigma x T))
            (Multiplicative.toAdd (Work.OROneRel.sigma y T)) w * c⁻¹) y from by
          rw [Work.OROneRel.magRewRel, Work.OROneRel.magnet,
            Work.OROneRel.magRew_zero_eq_rewrite]]
        exact Work.OROneRel.rho_magnet _ y hεw
      rw [hmr1, map_one] at hmr
      exact hmr.symm
    have h4 : Work.OROneRel.subst y x (Multiplicative.toAdd (Work.OROneRel.sigma x T))
        (Multiplicative.toAdd (Work.OROneRel.sigma y T)) w = 1 := by
      have h5 : Work.OROneRel.subst y x (Multiplicative.toAdd (Work.OROneRel.sigma x T))
          (Multiplicative.toAdd (Work.OROneRel.sigma y T)) w
          = c⁻¹ * (c * Work.OROneRel.subst y x
              (Multiplicative.toAdd (Work.OROneRel.sigma x T))
              (Multiplicative.toAdd (Work.OROneRel.sigma y T)) w * c⁻¹) * c := by group
      rw [h5, h2]; simp
    exact hsubst_w_ne h4
  -- the base relator is strictly shorter than `T`
  have hnormT : Work.OROneRel.letterCountNot y T < Work.OROneRel.relatorNorm T := by
    have h2 : Work.OROneRel.nt y (FreeGroup.toWord T) < Work.OROneRel.relatorNorm T :=
      Work.OROneRel.nt_lt_relatorNorm (r := T) (t := y) hy
    have h3 : Work.OROneRel.letterCountNot y T = Work.OROneRel.nt y (FreeGroup.toWord T) := by
      rw [Work.OROneRel.nt_eq_countP]
      rfl
    rwa [h3]
  have hMlt : Work.OROneRel.relatorNorm (Work.OROneRel.mmW y V) < Work.OROneRel.relatorNorm T := by
    rw [hMnorm]; exact hnormT
  have hMcyc : Work.OROneRel.IsCyclicallyReducedRelator (Work.OROneRel.mmW y V) :=
    Work.OROneRel.mmW_isCyclicallyReduced hVcyc hεV
  have hMpp : ¬ Work.OROneRel.IsProperPower (Work.OROneRel.mmW y V) :=
    Work.OROneRel.not_isProperPower_mmW hVpp hεV
  have hM := IH (Work.OROneRel.mmW y V) hMlt hMcyc hMpp
  -- its length is the number of non-`y` letters of the arc
  have hUnorm : Work.OROneRel.relatorNorm U = Work.OROneRel.letterCountNot y w := by
    have h1 : Work.OROneRel.relatorNorm U = (FreeGroup.toWord U).length := rfl
    rw [h1, hUlen]
  have hUlt : Work.OROneRel.relatorNorm U < Work.OROneRel.relatorNorm (Work.OROneRel.mmW y V) := by
    rw [hUnorm, hMnorm]; exact hylt
  -- the complementary arc of the base closes the argument
  by_cases hhalfU : 2 * Work.OROneRel.relatorNorm U ≤
      Work.OROneRel.relatorNorm (Work.OROneRel.mmW y V)
  · exact hM (k + 1) U hsubU hhalfU hU1 hmkU
  · push_neg at hhalfU
    obtain ⟨s, m', hsubs, hs1, hsnorm, hscontra⟩ :=
      Work.OROneRel.exists_complement_counterexample hMcyc hsubU hUlt hU1 hmkU
    refine hM m' s hsubs ?_ hs1 hscontra
    omega

end Work.OROneRel
