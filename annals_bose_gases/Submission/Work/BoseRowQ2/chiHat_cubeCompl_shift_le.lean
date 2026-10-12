import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Algebra.Order.Ring.Star
import Submission.Work.BoseRowQ2.chatTailAux
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

namespace Work.BoseRowQ2

local notation "Z3" => Fin 3 → ℤ

/-!
# `Work.BoseRowQ2.chiHat_cubeCompl_shift_le` — the shifted `|χ̂|`-tail outside the cube

The corpus bump `χ` is `C^∞` with compact support, so FS's decay lemma
(`Work.BoseK15.ChiReg_corpus`, `lem:DecaychiHat`) applied at order `52` gives

    `|χ̂(p)| · (1 + ‖p‖²)^52 ≤ Cchi`      for all `p`

(`χ̂ = Work.BoseRowQ2.chiHat`).  Feeding this into the dyadic lattice count
(`Work.BoseK15.sum_inv_one_add_norm_tail 52 101`, legal since `101 + 3 ≤ 2·52`) bounds the
`|χ̂|`-tail over lattice points of momentum at least `R ≥ 1` by `C/R^101`.  Since a point
`m ∉ cube N` has `‖vec (m − i)‖ ≥ rad N L` whenever `‖vec i‖ ≤ L` (`rad_le_norm_vec_sub`,
`BoseRowQ2/chatTailAux.lean`), the shifted sum over the cube complement obeys the same bound.

The two bricks are proved here: the finite-set tail bound `chiHat_abs_finset_tail_sum`, and
the passage to the `tsum` over the subtype `{m // m ∉ cube N}` by the usual nonnegativity
argument in `ℝ≥0∞` (the template is
`Submission/Work/BoseRowQ2/corpusBox_hatChi_sq_tsum_le.lean`).
-/

/-- **The finite-set `|χ̂|`-tail of the corpus bump.**  There is a constant `C ≥ 0` such that
for every `R ≥ 1` and every finite set `S` of lattice indices whose momenta `vec n = 2πn` all
have norm at least `R`, the sum of `|χ̂(vec n)|` over `S` is at most `C/R^101`.

Proof: `ChiReg_corpus 52` gives `|χ̂(p)|·(1+‖p‖²)^52 ≤ Cchi` (its *first* conjunct), i.e.
`|χ̂(vec n)| ≤ Cchi·(1+‖vec n‖²)^{-52}`; summing over `S` and applying the lattice tail
estimate `sum_inv_one_add_norm_tail 52 101` (legal since `101 + 3 ≤ 2·52`) gives the claim
with `C = Cchi·Ctail`. -/
theorem chiHat_abs_finset_tail_sum :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (R : ℝ) (S : Finset Z3), 1 ≤ R →
      (∀ n ∈ S, R ≤ ‖Work.BoseB4.vec n‖) →
      (∑ n ∈ S, |chiHat (Work.BoseB4.vec n)|) ≤ C / R ^ 101 := by
  obtain ⟨Cchi, hCchi_nn, hChi, _⟩ := Work.BoseK15.ChiReg_corpus 52
  obtain ⟨Ctail, _hCtail_nn, hCtail⟩ :=
    Work.BoseK15.sum_inv_one_add_norm_tail 52 101 (by norm_num)
  refine ⟨Cchi * Ctail, by positivity, ?_⟩
  intro R S hR hS
  have hpoint : ∀ n ∈ S, |chiHat (Work.BoseB4.vec n)|
      ≤ Cchi * (((1 : ℝ) + ‖Work.BoseB4.vec n‖ ^ 2) ^ 52)⁻¹ := by
    intro n _hn
    have hD : (0 : ℝ) < (1 + ‖Work.BoseB4.vec n‖ ^ 2) ^ 52 := by positivity
    have hle : |chiHat (Work.BoseB4.vec n)|
        ≤ Cchi / (1 + ‖Work.BoseB4.vec n‖ ^ 2) ^ 52 := by
      rw [le_div_iff₀ hD]
      simpa only [chiHat] using hChi (Work.BoseB4.vec n)
    simpa only [div_eq_mul_inv] using hle
  calc (∑ n ∈ S, |chiHat (Work.BoseB4.vec n)|)
      ≤ ∑ n ∈ S, Cchi * (((1 : ℝ) + ‖Work.BoseB4.vec n‖ ^ 2) ^ 52)⁻¹ :=
        Finset.sum_le_sum hpoint
    _ = Cchi * ∑ n ∈ S, (((1 : ℝ) + ‖Work.BoseB4.vec n‖ ^ 2) ^ 52)⁻¹ := by
        rw [Finset.mul_sum]
    _ ≤ Cchi * (Ctail / R ^ 101) :=
        mul_le_mul_of_nonneg_left (hCtail R S hR hS) hCchi_nn
    _ = (Cchi * Ctail) / R ^ 101 := by ring

/-- The `|χ̂|`-analogue of `chiHatSq_cubeCompl_shift_le`: for `‖vec i‖ ≤ L` and
`R := rad N L = 2π(N+1) − L ≥ 1`, the shifted `|χ̂|`-tail over the lattice points outside
the cube is `≤ C/R^101`.  Same reduction: `m ∉ cube N` gives `‖vec (m−i)‖ ≥ R`
(`rad_le_norm_vec_sub` in `BoseRowQ2/chatTailAux`), and the tail of `|χ̂|` is bounded at rate
`R^101` by the pointwise decay `|χ̂(p)|(1+‖p‖²)^52 ≤ Cchi` (`Work.BoseK15.ChiReg_corpus 52`)
together with `Work.BoseK15.sum_inv_one_add_norm_tail 52 101` (legal since `101 + 3 ≤ 2*52`);
the finite-set bound is upgraded to the subtype `tsum` by the nonnegativity passage used in
`Submission/Work/BoseRowQ2/corpusBox_hatChi_sq_tsum_le.lean`. -/
theorem chiHat_cubeCompl_shift_le :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (N : ℕ) (L : ℝ) (i : Fin 3 → ℤ), 0 ≤ L →
      1 ≤ Work.BoseRowQ2.rad N L → ‖Work.BoseB4.vec i‖ ≤ L →
      (∑' k : {k : Fin 3 → ℤ // k ∉ Work.BoseRowQ2.cube N},
        |Work.BoseRowQ2.chiHat (Work.BoseB4.vec (k.val - i))|)
        ≤ C / Work.BoseRowQ2.rad N L ^ 101 := by
  obtain ⟨C, hC0, hC⟩ := chiHat_abs_finset_tail_sum
  refine ⟨C, hC0, ?_⟩
  intro N L i _hL hR hi
  have hRpos : 0 < rad N L := lt_of_lt_of_le zero_lt_one hR
  have hB : 0 ≤ C / rad N L ^ 101 := div_nonneg hC0 (pow_pos hRpos 101).le
  -- the finite partial sums of the subtype `tsum` obey the finite-set tail bound
  have hfin : ∀ s : Finset {m : Z3 // m ∉ cube N},
      ∑ m ∈ s, |chiHat (Work.BoseB4.vec (m.val - i))| ≤ C / rad N L ^ 101 := by
    intro s
    have hinj : ∀ x ∈ s, ∀ y ∈ s, x.val - i = y.val - i → x = y := by
      intro x _hx y _hy hxy
      refine Subtype.ext (funext fun j => ?_)
      have h : x.val j - i j = y.val j - i j := congrFun hxy j
      omega
    have hsum : ∑ m ∈ s, |chiHat (Work.BoseB4.vec (m.val - i))|
        = ∑ n ∈ s.image (fun m : {m : Z3 // m ∉ cube N} => m.val - i),
            |chiHat (Work.BoseB4.vec n)| := by
      rw [Finset.sum_image hinj]
    rw [hsum]
    refine hC (rad N L) _ hR ?_
    intro n hn
    obtain ⟨m, _hm, rfl⟩ := Finset.mem_image.mp hn
    exact rad_le_norm_vec_sub m.2 hi
  -- pass to the `ℝ≥0∞` `tsum`: it is the supremum of the finite partial sums
  have hENN : (∑' m : {m : Z3 // m ∉ cube N},
        ENNReal.ofReal (|chiHat (Work.BoseB4.vec (m.val - i))|))
      ≤ ENNReal.ofReal (C / rad N L ^ 101) := by
    rw [ENNReal.tsum_eq_iSup_sum]
    refine iSup_le fun s => ?_
    rw [← ENNReal.ofReal_sum_of_nonneg (fun m _ => abs_nonneg _)]
    exact ENNReal.ofReal_le_ofReal (hfin s)
  have hne : (∑' m : {m : Z3 // m ∉ cube N},
      ENNReal.ofReal (|chiHat (Work.BoseB4.vec (m.val - i))|)) ≠ ⊤ :=
    ne_top_of_le_ne_top ENNReal.ofReal_ne_top hENN
  have htoReal : (∑' m : {m : Z3 // m ∉ cube N},
        ENNReal.ofReal (|chiHat (Work.BoseB4.vec (m.val - i))|)).toReal
      = ∑' m : {m : Z3 // m ∉ cube N}, |chiHat (Work.BoseB4.vec (m.val - i))| := by
    rw [ENNReal.tsum_toReal_eq (fun m => ENNReal.ofReal_ne_top)]
    exact tsum_congr fun m => ENNReal.toReal_ofReal (abs_nonneg _)
  calc (∑' k : {k : Z3 // k ∉ cube N}, |chiHat (Work.BoseB4.vec (k.val - i))|)
      = (∑' m : {m : Z3 // m ∉ cube N},
          ENNReal.ofReal (|chiHat (Work.BoseB4.vec (m.val - i))|)).toReal := htoReal.symm
    _ ≤ (ENNReal.ofReal (C / rad N L ^ 101)).toReal :=
        ENNReal.toReal_mono ENNReal.ofReal_ne_top hENN
    _ = C / rad N L ^ 101 := ENNReal.toReal_ofReal hB

end Work.BoseRowQ2
