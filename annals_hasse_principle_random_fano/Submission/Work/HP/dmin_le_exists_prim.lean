import Mathlib
import Submission.Work.HP.Defs
import Submission.Work.HP.PairsAux
import Submission.Work.HP.HPgram
import Submission.Work.HP.gramMat_det_le
import Submission.Work.HP.exists_prim_super
import Submission.Work.HP.exists_sub_lat_pair

/-!
# `dmin_le_exists_prim`

If `𝔡_r(x,y) ≤ D` there is a **primitive** (saturated) rank-`r` sublattice of `ℤ^ι` containing
both `x` and `y` whose determinant is at most `D + 1`.

The paper (Browning--Le Boudec--Sawin, §"On the typical size of some key quantities") records
that the infimum defining `𝔡_r(x,y)` is attained by primitive lattices: the determinant of a
lattice is *larger* than the determinant of its saturation, so a minimising lattice can be
replaced by its saturation.

Formally `dmin r S = sInf {detL L | L of rank r containing S}`, so the hypothesis `≤ D` only
produces lattices of determinant `< D + 1`.  The set of determinants is nonempty
(`exists_sub_lat_pair`) and bounded below by `0` (`detL_nonneg_gram`), so `csInf_lt_iff` gives a
rank-`r` lattice `L ∋ x, y` with `detL L < D + 1`; `exists_prim_super` replaces `L` by a
primitive lattice `P ⊇ L` of the same rank, and monotonicity of `detL` under inclusions of
lattices of equal rank (`detL_le_of_le_of_rank_eq`) gives `detL P ≤ detL L < D + 1`.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

noncomputable section

namespace Work.HP

/-- Monotonicity of `detL` under inclusions of lattices of equal rank: an inclusion of lattices
of the same rank has finite index `≥ 1`, and `detL` is the covolume in the common real span, so it
can only decrease. -/
theorem detL_le_of_le_of_rank_eq {ι : Type*} [Fintype ι] [DecidableEq ι]
    {L M : Submodule ℤ (ι → ℤ)} (hLM : L ≤ M) (hrk : rk L = rk M) : detL M ≤ detL L := by
  have h1 : Module.finrank ℤ L = (Submodule.basisOfPid (Pi.basisFun ℤ ι) L).1 := by
    rw [Module.finrank_eq_card_basis (Submodule.basisOfPid (Pi.basisFun ℤ ι) L).2]; simp
  have h2 : Module.finrank ℤ M = (Submodule.basisOfPid (Pi.basisFun ℤ ι) M).1 := by
    rw [Module.finrank_eq_card_basis (Submodule.basisOfPid (Pi.basisFun ℤ ι) M).2]; simp
  have hk : (Submodule.basisOfPid (Pi.basisFun ℤ ι) L).1
      = (Submodule.basisOfPid (Pi.basisFun ℤ ι) M).1 := by rw [← h1, ← h2]; exact hrk
  rw [detL_eq_sqrt_gramMat L, detL_eq_sqrt_gramMat M]
  exact Real.sqrt_le_sqrt (gramMat_det_le_of_le' hk _ _ hLM)

theorem dmin_le_exists_prim (ι : Type) [Fintype ι] [DecidableEq ι] (r : ℕ)
    (x y : ι → ℤ) (D : ℝ) (hxy : LinearIndependent ℤ ![x, y])
    (hr : 2 ≤ r) (hrN : r ≤ Fintype.card ι) (hd : dmin r {x, y} ≤ D) :
    ∃ L : Submodule ℤ (ι → ℤ), IsPrimLat L ∧ rk L = r ∧ x ∈ L ∧ y ∈ L ∧ detL L ≤ D + 1 := by
  set S : Set ℝ := {E : ℝ | ∃ L : Submodule ℤ (ι → ℤ),
    rk L = r ∧ ({x, y} : Set (ι → ℤ)) ⊆ L ∧ detL L = E} with hS
  have hne : S.Nonempty := by
    obtain ⟨L, hrank, hxL, hyL⟩ := exists_sub_lat_pair r x y hxy hr hrN
    refine ⟨detL L, L, hrank, ?_, rfl⟩
    intro z hz
    rcases hz with rfl | rfl
    · exact hxL
    · exact hyL
  have hbd : BddBelow S := by
    refine ⟨0, ?_⟩
    rintro e ⟨L, -, -, hdet⟩
    rw [← hdet]
    exact detL_nonneg_gram L
  have hlt : sInf S < D + 1 := by
    have h : sInf S ≤ D := by
      rw [hS]
      exact hd
    linarith
  obtain ⟨e, ⟨L, hrank, hsub, hdet⟩, helt⟩ := (csInf_lt_iff hbd hne).mp hlt
  obtain ⟨P, hLP, hPprim, hPrank⟩ := exists_prim_super L
  have hxL : x ∈ L := hsub (by simp)
  have hyL : y ∈ L := hsub (by simp)
  refine ⟨P, hPprim, by rw [hPrank, hrank], hLP hxL, hLP hyL, ?_⟩
  have hmono := detL_le_of_le_of_rank_eq hLP (by rw [hPrank, hrank])
  rw [← hdet] at helt
  linarith

end Work.HP
