import Mathlib
import Submission.Work.ANALYTIC.HaarDefs
import Submission.Work.ATOM.ZS.Unred.ExtEnum

/-!
# The Haar/Schauder basis of `C(T,ℤ)`: elementary level facts

This file collects the elementary combinatorial facts about the level structure
`Work.ATOM.LevelData` which are used to prove that `{fJ T j | j : JIdx}` is a `ℤ`-basis of
`LC T = LocallyConstant ↥T ℤ` with dual coordinates `phiJ T`.

* `Haar.lvlFinset T N` — the (finite) set of `j : ℕ` with `lvl T j ≤ N`;
* `Haar.newFinset T N` — the (finite) set of `j : ℕ` with `lvl T j = N`;
* `Haar.fCyl_apply'` — `fCyl T j x = if e_{n(j)} x = a_j then 1 else 0`;
* `Haar.a_mem_A_iff` and `Haar.exists_a_eq_of_mem_A_succ_not_mem_A` — the description of the
  "new points" of a level;
* `Haar.pre T N g` — the level-`N` part `x ↦ g (e_N x)` of `g : LC T`, with `Haar.phi_pre`;
* the linearity of `phi` and `phiJ` in the function argument.
-/

open CategoryTheory Limits LightProfinite LightCondensed MonoidalCategory MonoidalClosed
open OnePoint

attribute [local instance] Classical.propDecidable

noncomputable section

namespace Work.ANALYTIC

namespace Haar

variable (T : LightProfinite.{0}) [Infinite T]

/-- The level `n(j) = lv (a j)` of the `j`-th new point (an abbreviation of `Work.ATOM.lvl`). -/
abbrev lvl (j : ℕ) : ℕ := Work.ATOM.lvl T j

/-- `JIdx = OnePoint ℕ` is definitionally `Option ℕ`, but `OnePoint` is a semi-reducible
definition, so instance search does not find `DecidableEq` for it.  We register the instance
explicitly (with a name of its own, so that other files may register their own without a clash). -/
instance haarJIdxDecidableEq : DecidableEq JIdx :=
  inferInstanceAs (DecidableEq (Option ℕ))

/-! ## The index sets of the levels -/

/-- The finite set of the indices `j` of level `≤ N`. -/
abbrev lvlFinset (N : ℕ) : Finset ℕ :=
  (Finset.range (N + 1)).biUnion fun k => (Work.ATOM.levelData_finite_level (S := T) k).toFinset

/-- The finite set of the indices `j` of level exactly `N`. -/
abbrev newFinset (N : ℕ) : Finset ℕ :=
  (Work.ATOM.levelData_finite_level (S := T) N).toFinset

theorem mem_newFinset {N j : ℕ} : j ∈ newFinset T N ↔ lvl T j = N :=
  Set.Finite.mem_toFinset _

theorem mem_lvlFinset {N j : ℕ} : j ∈ lvlFinset T N ↔ lvl T j ≤ N := by
  rw [lvlFinset, Finset.mem_biUnion]
  constructor
  · rintro ⟨k, hk, hjk⟩
    rw [Finset.mem_range] at hk
    rw [mem_newFinset] at hjk
    omega
  · intro h
    exact ⟨lvl T j, by rw [Finset.mem_range]; omega, by rw [mem_newFinset]⟩

theorem lvlFinset_succ (N : ℕ) : lvlFinset T (N + 1) = lvlFinset T N ∪ newFinset T (N + 1) := by
  ext j
  simp only [mem_lvlFinset, Finset.mem_union, mem_newFinset]
  omega

theorem disjoint_lvlFinset_newFinset (N : ℕ) :
    Disjoint (lvlFinset T N) (newFinset T (N + 1)) := by
  rw [Finset.disjoint_left]
  intro j hj1 hj2
  rw [mem_lvlFinset] at hj1
  rw [mem_newFinset] at hj2
  omega

/-! ## Elementary facts about `e`, `π` and `σ` -/

/-- `π_m (e_n x) = leg n m (π_n x)`. -/
theorem proj_e_apply (n m : ℕ) (x : ↥T) :
    T.proj m (Work.ATOM.e T n x) = Work.ATOM.leg T n m (T.proj n x) := by
  rw [Work.ATOM.e_apply, Work.ATOM.proj_sig_apply]

/-- `π_n` is fixed by `e_n`. -/
theorem proj_e_self (n : ℕ) (x : ↥T) : T.proj n (Work.ATOM.e T n x) = T.proj n x := by
  rw [proj_e_apply, Work.ATOM.leg_of_le T n n le_rfl, Work.ATOM.itTr_self]
  rfl

/-- `e_n (e_m x) = e_(min m n) x`. -/
theorem e_comp_apply (m n : ℕ) (x : ↥T) :
    Work.ATOM.e T n (Work.ATOM.e T m x) = Work.ATOM.e T (min m n) x := by
  have h := ConcreteCategory.congr_hom (Work.ATOM.e_comp T m n) x
  simpa only [CategoryTheory.comp_apply] using h

theorem e_idem (n : ℕ) (x : ↥T) : Work.ATOM.e T n (Work.ATOM.e T n x) = Work.ATOM.e T n x := by
  rw [e_comp_apply, min_self]

theorem e_fix_s₀ (n : ℕ) :
    Work.ATOM.e T n (Work.ATOM.levelData T).s₀ = (Work.ATOM.levelData T).s₀ :=
  (Work.ATOM.levelData T).e_fix n

/-! ## The cylinder condition -/

/-- The two conditions defining the cylinder of `a_j` are equivalent. -/
theorem proj_eq_proj_iff (j : ℕ) (x : ↥T) :
    T.proj (lvl T j) x = T.proj (lvl T j) ((Work.ATOM.levelData T).a j) ↔
      Work.ATOM.e T (lvl T j) x = (Work.ATOM.levelData T).a j := by
  constructor
  · intro h
    calc Work.ATOM.e T (lvl T j) x
        = Work.ATOM.sig T (lvl T j) (T.proj (lvl T j) x) := Work.ATOM.e_apply T _ x
      _ = Work.ATOM.sig T (lvl T j) (T.proj (lvl T j) ((Work.ATOM.levelData T).a j)) := by rw [h]
      _ = Work.ATOM.e T (lvl T j) ((Work.ATOM.levelData T).a j) := (Work.ATOM.e_apply T _ _).symm
      _ = (Work.ATOM.levelData T).a j := Work.ATOM.levelData_e_lvl_a j
  · intro h
    calc T.proj (lvl T j) x = T.proj (lvl T j) (Work.ATOM.e T (lvl T j) x) :=
          (proj_e_self T (lvl T j) x).symm
      _ = T.proj (lvl T j) ((Work.ATOM.levelData T).a j) := by rw [h]

/-- The defining values of `f_j`, in the form used by the inductive expansion. -/
theorem fCyl_apply' (j : ℕ) (x : ↥T) :
    fCyl T j x =
      if Work.ATOM.e T (lvl T j) x = (Work.ATOM.levelData T).a j then 1 else 0 := by
  rw [fCyl_apply]
  by_cases h : Work.ATOM.e T (lvl T j) x = (Work.ATOM.levelData T).a j
  · rw [if_pos ((proj_eq_proj_iff T j x).mpr h), if_pos h]
  · rw [if_neg (fun hc => h ((proj_eq_proj_iff T j x).mp hc)), if_neg h]

/-- **`f_j(x) = 1` iff `e_{n(j)} x = a_j`.** -/
theorem fCyl_apply_iff (j : ℕ) (x : ↥T) :
    fCyl T j x = 1 ↔ Work.ATOM.e T (lvl T j) x = (Work.ATOM.levelData T).a j := by
  rw [fCyl_apply']
  by_cases h : Work.ATOM.e T (lvl T j) x = (Work.ATOM.levelData T).a j <;> simp [h]

/-! ## The sets `A N` and the new points -/

/-- `a_j ∈ A N` iff `lvl j ≤ N`. -/
theorem a_mem_A_iff {j N : ℕ} :
    (Work.ATOM.levelData T).a j ∈ Work.ATOM.A T N ↔ lvl T j ≤ N := by
  constructor
  · intro h
    exact Work.ATOM.levelData_lv_le h
  · intro h
    exact Work.ATOM.A_mono_le T h
      ((Work.ATOM.levelData T).lv_mem _ (Work.ATOM.levelData_a_mem j))

theorem a_mem_A_succ {j N : ℕ} (h : lvl T j = N + 1) :
    (Work.ATOM.levelData T).a j ∈ Work.ATOM.A T (N + 1) :=
  (a_mem_A_iff T).mpr (le_of_eq h)

theorem notMem_A_of_lvl_eq {j N : ℕ} (h : lvl T j = N + 1) :
    (Work.ATOM.levelData T).a j ∉ Work.ATOM.A T N := by
  rw [a_mem_A_iff]
  omega

theorem s₀_mem_A (N : ℕ) : (Work.ATOM.levelData T).s₀ ∈ Work.ATOM.A T N :=
  Work.ATOM.A_mono_le T (Nat.zero_le N) (Work.ATOM.levelData T).mem_A0

/-- `e_k x ∈ A k`. -/
theorem e_mem_A (k : ℕ) (x : ↥T) : Work.ATOM.e T k x ∈ Work.ATOM.A T k := ⟨x, rfl⟩

/-- **The new points of level `N+1` are exactly the `a_j` with `lvl j = N+1`.** -/
theorem exists_a_eq_of_mem_A_succ_not_mem_A {N : ℕ} {y : ↥T}
    (h1 : y ∈ Work.ATOM.A T (N + 1)) (h2 : y ∉ Work.ATOM.A T N) :
    ∃ j : ℕ, lvl T j = N + 1 ∧ (Work.ATOM.levelData T).a j = y := by
  have hy : y ∈ Work.ATOM.levelSet T := Set.mem_iUnion.mpr ⟨N + 1, h1⟩
  have hne : y ≠ (Work.ATOM.levelData T).s₀ := by
    intro h
    exact h2 (h ▸ s₀_mem_A T N)
  obtain ⟨j, hj⟩ : ∃ j, (Work.ATOM.levelData T).a j = y := by
    rcases (Work.ATOM.levelData_mem_levelSet_iff y).mp hy with h | h
    · exact h
    · exact absurd h hne
  refine ⟨j, ?_, hj⟩
  have hle : (Work.ATOM.levelData T).lv y ≤ N + 1 := Work.ATOM.levelData_lv_le h1
  have hlt : ¬ (Work.ATOM.levelData T).lv y ≤ N := by
    intro h
    exact h2 (Work.ATOM.A_mono_le T h ((Work.ATOM.levelData T).lv_mem y hy))
  change (Work.ATOM.levelData T).lv ((Work.ATOM.levelData T).a j) = N + 1
  rw [hj]
  omega

/-- The points of `A 0` are the base point and the `a_j` of level `0`. -/
theorem eq_s₀_or_exists_of_mem_A_zero {y : ↥T} (h : y ∈ Work.ATOM.A T 0) :
    y = (Work.ATOM.levelData T).s₀ ∨
      ∃ j : ℕ, lvl T j = 0 ∧ (Work.ATOM.levelData T).a j = y := by
  by_cases hne : y = (Work.ATOM.levelData T).s₀
  · exact Or.inl hne
  · refine Or.inr ?_
    have hy : y ∈ Work.ATOM.levelSet T := Set.mem_iUnion.mpr ⟨0, h⟩
    obtain ⟨j, hj⟩ : ∃ j, (Work.ATOM.levelData T).a j = y := by
      rcases (Work.ATOM.levelData_mem_levelSet_iff y).mp hy with h' | h'
      · exact h'
      · exact absurd h' hne
    refine ⟨j, ?_, hj⟩
    have hle : (Work.ATOM.levelData T).lv y ≤ 0 := Work.ATOM.levelData_lv_le h
    change (Work.ATOM.levelData T).lv ((Work.ATOM.levelData T).a j) = 0
    rw [hj]
    omega

/-! ## The parent of a new point -/

/-- `par j ∈ A N` when `lvl j ≤ N`, so that `e_N` fixes it. -/
theorem par_mem_A {N j : ℕ} (hj : lvl T j ≤ N) : par T j ∈ Work.ATOM.A T N := by
  rw [par]
  split_ifs with h
  · exact s₀_mem_A T N
  · exact Work.ATOM.A_mono_le T (by omega)
      (e_mem_A T (lvl T j - 1) ((Work.ATOM.levelData T).a j))

/-- `e_N` fixes `par j` when `lvl j ≤ N`. -/
theorem e_par_of_lvl_le {N j : ℕ} (hj : lvl T j ≤ N) :
    Work.ATOM.e T N (par T j) = par T j :=
  Work.ATOM.e_fixes_of_mem_A T (par_mem_A T hj)

theorem e_a_of_lvl_le {N j : ℕ} (hj : lvl T j ≤ N) :
    Work.ATOM.e T N ((Work.ATOM.levelData T).a j) = (Work.ATOM.levelData T).a j :=
  Work.ATOM.e_fixes_of_mem_A T ((a_mem_A_iff T).mpr hj)

/-! ## The level-`N` part of a locally constant function -/

/-- The level-`N` part `x ↦ g (e_N x)` of `g : LC T`. -/
def pre (N : ℕ) (g : LC T) : LC T := g.comap (Work.ATOM.e T N).hom.hom

theorem pre_apply (N : ℕ) (g : LC T) (x : ↥T) : pre T N g x = g (Work.ATOM.e T N x) := by
  rw [pre, LocallyConstant.coe_comap]
  rfl

theorem pre_self (N : ℕ) (g : LC T) : pre T N (pre T N g) = pre T N g := by
  ext x
  rw [pre_apply, pre_apply, pre_apply, e_idem]

theorem pre_s₀ (N : ℕ) (g : LC T) :
    pre T N g ((Work.ATOM.levelData T).s₀) = g ((Work.ATOM.levelData T).s₀) := by
  rw [pre_apply, e_fix_s₀]

/-- The coordinates of the level-`N` part, at a level `≤ N`. -/
theorem phi_pre {N j : ℕ} (hj : lvl T j ≤ N) (g : LC T) : phi T j (pre T N g) = phi T j g := by
  rw [phi, phi, pre_apply, pre_apply, e_a_of_lvl_le T hj, e_par_of_lvl_le T hj]

/-! ## The pairing is linear in the function -/

theorem phi_add (j : ℕ) (g g' : LC T) : phi T j (g + g') = phi T j g + phi T j g' := by
  rw [phi, phi, phi, LocallyConstant.add_apply, LocallyConstant.add_apply]
  ring

theorem phi_sub (j : ℕ) (g g' : LC T) : phi T j (g - g') = phi T j g - phi T j g' := by
  rw [phi, phi, phi, LocallyConstant.sub_apply, LocallyConstant.sub_apply]
  ring

theorem phi_smul (j : ℕ) (c : ℤ) (g : LC T) : phi T j (c • g) = c * phi T j g := by
  rw [phi, phi, LocallyConstant.smul_apply, LocallyConstant.smul_apply, smul_eq_mul, smul_eq_mul]
  ring

theorem phi_neg (j : ℕ) (g : LC T) : phi T j (-g) = -phi T j g := by
  rw [phi, phi, LocallyConstant.neg_apply, LocallyConstant.neg_apply]
  ring

theorem phiJ_add (j : JIdx) (g g' : LC T) : phiJ T j (g + g') = phiJ T j g + phiJ T j g' := by
  induction j using OnePoint.rec with
  | infty => rw [phiJ_inf, phiJ_inf, phiJ_inf, LocallyConstant.add_apply]
  | coe n =>
      rw [phiJ_coe, phiJ_coe, phiJ_coe]
      exact phi_add T n g g'

theorem phiJ_sub (j : JIdx) (g g' : LC T) : phiJ T j (g - g') = phiJ T j g - phiJ T j g' := by
  induction j using OnePoint.rec with
  | infty => rw [phiJ_inf, phiJ_inf, phiJ_inf, LocallyConstant.sub_apply]
  | coe n =>
      rw [phiJ_coe, phiJ_coe, phiJ_coe]
      exact phi_sub T n g g'

theorem phiJ_smul (j : JIdx) (c : ℤ) (g : LC T) : phiJ T j (c • g) = c * phiJ T j g := by
  induction j using OnePoint.rec with
  | infty => rw [phiJ_inf, phiJ_inf, LocallyConstant.smul_apply, smul_eq_mul]
  | coe n =>
      rw [phiJ_coe, phiJ_coe]
      exact phi_smul T n c g

end Haar

end Work.ANALYTIC
