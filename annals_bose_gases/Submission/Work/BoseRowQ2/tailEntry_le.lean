import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Algebra.Order.Star.Real
import Submission.Work.BoseRowQ2.chatTailAux
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Work.BoseRowQ2.tailEntry_le` — the lattice-tail *entry* bound of the sharp mask row

The tail matrix of the sharp mask row is

    `Tail N i j = ∑' m : {m : ℤ³ // m ∉ cube N},
        χ̂(vec (m − K i)) · χ̂(vec (m − K j))`      (`Work.BoseRowQ2.tail_eq_tsum`),

i.e. the contribution of the lattice points *outside* the fundamental cube to the lattice
Parseval identity of the corpus bump.  This module proves the **entry bound**: there is an
absolute constant `C ≥ 0` with

    `|∑'_{m ∉ cube N} χ̂(vec (m − a)) χ̂(vec (m − c))| ≤ C / (2π(N+1) − L)^101`

for every pair of lattice vectors `a`, `c` of momentum norm at most `L`, and every `N`, `L`
with `2π(N+1) − L ≥ 1`.  This is the sharp-mask analogue of the `χ̂²`-tail estimate
`Work.BoseRowQ2.chiTailC_le` (`∑_{‖vec n‖ ≥ R} χ̂(vec n)² ≤ chiTailC/R^101`), and it is the one
input of the quadratic-form bound `Work.BoseRowQ2.tail_quad_le`.

## The argument

1. **Decay of the corpus `χ̂`.**  `Work.BoseK15.ChiReg_corpus 52` (FS `lem:DecaychiHat`) gives
   `|χ̂(p)| ≤ Cchi/(1+‖p‖²)^52`, hence the squared form `χ̂(p)² ≤ Cchi²/(1+‖p‖²)^104`.
2. **The lattice geometry** (`Work.BoseRowQ2.chatTailAux`).  If `m ∉ cube N` and
   `‖vec i‖ ≤ L` then `‖vec (m − i)‖ ≥ rad N L := 2π(N+1) − L`, so the *shifted* index sits in
   the lattice tail of radius `R := rad N L`.
3. **The shifted tail.**  Summing the squared decay over the complement of the cube and
   reindexing by the translation `m ↦ m − a` embeds that index set into the tail subtype
   `{n // R ≤ ‖vec n‖}`; `Summable.tsum_le_tsum_of_inj` plus `Work.BoseRowQ2.chiTailC_le` bounds
   the shifted `χ̂²`-tail by `chiTailC/R^101`.  The two summability inputs are the shifted lattice
   majorant (`Work.BoseK15.sum_inv_one_add_norm_le` transported by the translation
   `Equiv.subRight a`).
4. **Assembly.**  `2|xy| ≤ x² + y²` splits the modulus of the product into the two squared
   shifted tails, and `norm_tsum_le_tsum_norm` bounds the modulus of the `tsum` by the `tsum`
   of the moduli.  The constant produced is `2·chiTailC`.
-/

noncomputable section

open scoped BigOperators

namespace Work.BoseRowQ2

local notation "Z3" => Fin 3 → ℤ

/-! ## 1. The shifted lattice majorant is summable -/

private theorem summable_shift_majorant (a : Z3) (s : ℕ) (hs : 3 < 2 * s) :
    Summable (fun m : Z3 => (((1 : ℝ) + ‖Work.BoseB4.vec (m - a)‖ ^ 2) ^ s)⁻¹) := by
  obtain ⟨C0, _hC0nn, hC0⟩ := Work.BoseK15.sum_inv_one_add_norm_le s hs
  have hbase : Summable (fun n : Z3 => (((1 : ℝ) + ‖Work.BoseB4.vec n‖ ^ 2) ^ s)⁻¹) :=
    summable_of_sum_le (fun n => by positivity) hC0
  have h := (Equiv.summable_iff (Equiv.subRight a)
    (f := fun n : Z3 => (((1 : ℝ) + ‖Work.BoseB4.vec n‖ ^ 2) ^ s)⁻¹)).mpr hbase
  exact h.congr (fun m => by simp [Function.comp, Equiv.subRight_apply])

/-! ## 2. The pointwise decay of `χ̂`, squared -/

private theorem chiHat_sq_decay :
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ p : EuclideanSpace ℝ (Fin 3), chiHat p ^ 2 ≤ C / (1 + ‖p‖ ^ 2) ^ 104 := by
  obtain ⟨C, hC0, hC⟩ := Work.BoseK15.ChiReg_corpus 52
  have hC' : ∀ p : EuclideanSpace ℝ (Fin 3), |chiHat p| ≤ C / (1 + ‖p‖ ^ 2) ^ 52 := fun p => by
    have hD : 0 < (1 + ‖p‖ ^ 2) ^ 52 := by positivity
    rw [chiHat, le_div_iff₀ hD]
    exact hC.1 p
  refine ⟨C ^ 2, by positivity, fun p => ?_⟩
  have hD : 0 < (1 + ‖p‖ ^ 2) ^ 52 := by positivity
  have habs : |chiHat p| ≤ C / (1 + ‖p‖ ^ 2) ^ 52 := hC' p
  have hK : 0 ≤ C / (1 + ‖p‖ ^ 2) ^ 52 := div_nonneg hC0 hD.le
  have hpow : (((1 : ℝ) + ‖p‖ ^ 2) ^ 52) ^ 2 = ((1 : ℝ) + ‖p‖ ^ 2) ^ 104 := by rw [← pow_mul]
  calc chiHat p ^ 2 ≤ (C / (1 + ‖p‖ ^ 2) ^ 52) ^ 2 := by
        rw [sq_le_sq, abs_of_nonneg hK]; exact habs
    _ = C ^ 2 / ((1 + ‖p‖ ^ 2) ^ 104) := by rw [div_pow, hpow]

/-! ## 3. Summability of the shifted `χ̂²`-tails -/

private theorem summable_chiHat_sq_shift (N : ℕ) (a : Z3) :
    Summable (fun m : {m : Z3 // m ∉ cube N} => chiHat (Work.BoseB4.vec (m.val - a)) ^ 2) := by
  obtain ⟨Cchi, _hCchi0, hChi⟩ := chiHat_sq_decay
  refine Summable.of_nonneg_of_le
    (f := fun m : {m : Z3 // m ∉ cube N} =>
      Cchi * (((1 : ℝ) + ‖Work.BoseB4.vec (m.val - a)‖ ^ 2) ^ 104)⁻¹)
    (fun m => sq_nonneg _) (fun m => ?_) ?_
  · simpa [div_eq_mul_inv] using hChi (Work.BoseB4.vec (m.val - a))
  · exact ((summable_shift_majorant a 104 (by norm_num)).subtype _).mul_left _

private theorem summable_chiHat_sq_tail (R : ℝ) :
    Summable (fun n : {n : Z3 // R ≤ ‖Work.BoseB4.vec n‖} =>
      chiHat (Work.BoseB4.vec n.val) ^ 2) := by
  obtain ⟨Cchi, _hCchi0, hChi⟩ := chiHat_sq_decay
  refine Summable.of_nonneg_of_le
    (f := fun n : {n : Z3 // R ≤ ‖Work.BoseB4.vec n‖} =>
      Cchi * (((1 : ℝ) + ‖Work.BoseB4.vec n.val‖ ^ 2) ^ 104)⁻¹)
    (fun n => sq_nonneg _) (fun n => ?_) ?_
  · simpa [div_eq_mul_inv] using hChi (Work.BoseB4.vec n.val)
  · have h := (summable_shift_majorant (0 : Z3) 104 (by norm_num)).subtype
      (fun m : Z3 => R ≤ ‖Work.BoseB4.vec m‖)
    simpa [sub_zero] using h.mul_left _

/-! ## 4. The shifted `χ̂²`-tail -/

/-- **The shifted `χ̂²`-tail of the corpus bump.**  For every lattice point `a` with
`‖vec a‖ ≤ L`, the sum of `χ̂(vec (m − a))²` over the lattice points `m` *outside* the cube
`[−N,N]³` is at most `chiTailC/(2π(N+1) − L)^101`.  The shift is absorbed by the geometric
observation `Work.BoseRowQ2.rad_le_norm_vec_sub`: every shifted index has momentum at least
`rad N L`. -/
private theorem shifted_sq_tsum_le (N : ℕ) (L : ℝ) (hR : 1 ≤ rad N L) (a : Z3)
    (ha : ‖Work.BoseB4.vec a‖ ≤ L) :
    (∑' m : {m : Z3 // m ∉ cube N}, chiHat (Work.BoseB4.vec (m.val - a)) ^ 2)
      ≤ chiTailC / (rad N L) ^ 101 := by
  have hinj : Function.Injective
      (fun m : {m : Z3 // m ∉ cube N} =>
        (⟨m.val - a, rad_le_norm_vec_sub m.2 ha⟩ :
          {n : Z3 // rad N L ≤ ‖Work.BoseB4.vec n‖})) := by
    intro m₁ m₂ h
    have h' : m₁.val - a = m₂.val - a := congrArg Subtype.val h
    have h'' := congrArg (fun z : Z3 => z + a) h'
    rw [sub_add_cancel, sub_add_cancel] at h''
    exact Subtype.ext h''
  have hle := Summable.tsum_le_tsum_of_inj
    (f := fun m : {m : Z3 // m ∉ cube N} => chiHat (Work.BoseB4.vec (m.val - a)) ^ 2)
    (g := fun n : {n : Z3 // rad N L ≤ ‖Work.BoseB4.vec n‖} =>
      chiHat (Work.BoseB4.vec n.val) ^ 2)
    (fun m => (⟨m.val - a, rad_le_norm_vec_sub m.2 ha⟩ :
      {n : Z3 // rad N L ≤ ‖Work.BoseB4.vec n‖}))
    hinj (fun c _ => sq_nonneg _) (fun i => le_refl _)
    (summable_chiHat_sq_shift N a) (summable_chiHat_sq_tail (rad N L))
  exact le_trans hle (chiTailC_le (rad N L) hR)

/-! ## 5. The entry bound -/

theorem tailEntry_le :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (N : ℕ) (L : ℝ), 0 ≤ L →
      1 ≤ 2 * Real.pi * ((N : ℝ) + 1) - L →
      ∀ (a c : Fin 3 → ℤ),
        ‖Work.BoseB4.vec a‖ ≤ L → ‖Work.BoseB4.vec c‖ ≤ L →
      |tsum (fun m : {m : Fin 3 → ℤ // m ∉ Work.BoseRowQ2.cube N} =>
          Work.BoseRowQ2.chiHat (Work.BoseB4.vec (m.val - a))
            * Work.BoseRowQ2.chiHat (Work.BoseB4.vec (m.val - c)))|
        ≤ C / (2 * Real.pi * ((N : ℝ) + 1) - L) ^ 101 := by
  refine ⟨2 * chiTailC, mul_nonneg (by norm_num) chiTailC_nonneg, ?_⟩
  intro N L _hL hR a c ha hc
  have hsq_a : (∑' m : {m : Z3 // m ∉ cube N}, chiHat (Work.BoseB4.vec (m.val - a)) ^ 2)
      ≤ chiTailC / (rad N L) ^ 101 := shifted_sq_tsum_le N L hR a ha
  have hsq_c : (∑' m : {m : Z3 // m ∉ cube N}, chiHat (Work.BoseB4.vec (m.val - c)) ^ 2)
      ≤ chiTailC / (rad N L) ^ 101 := shifted_sq_tsum_le N L hR c hc
  have hsum_a : Summable (fun m : {m : Z3 // m ∉ cube N} =>
      chiHat (Work.BoseB4.vec (m.val - a)) ^ 2) := summable_chiHat_sq_shift N a
  have hsum_c : Summable (fun m : {m : Z3 // m ∉ cube N} =>
      chiHat (Work.BoseB4.vec (m.val - c)) ^ 2) := summable_chiHat_sq_shift N c
  have hle : ∀ m : {m : Z3 // m ∉ cube N},
      |chiHat (Work.BoseB4.vec (m.val - a)) * chiHat (Work.BoseB4.vec (m.val - c))|
        ≤ chiHat (Work.BoseB4.vec (m.val - a)) ^ 2
          + chiHat (Work.BoseB4.vec (m.val - c)) ^ 2 := by
    intro m
    rw [abs_mul]
    have h := sq_nonneg (|chiHat (Work.BoseB4.vec (m.val - a))|
      - |chiHat (Work.BoseB4.vec (m.val - c))|)
    have h1 : |chiHat (Work.BoseB4.vec (m.val - a))| ^ 2
        = chiHat (Work.BoseB4.vec (m.val - a)) ^ 2 := sq_abs _
    have h2 : |chiHat (Work.BoseB4.vec (m.val - c))| ^ 2
        = chiHat (Work.BoseB4.vec (m.val - c)) ^ 2 := sq_abs _
    nlinarith [h, h1, h2]
  have hsum_abs : Summable (fun m : {m : Z3 // m ∉ cube N} =>
      |chiHat (Work.BoseB4.vec (m.val - a)) * chiHat (Work.BoseB4.vec (m.val - c))|) :=
    Summable.of_nonneg_of_le
      (f := fun m : {m : Z3 // m ∉ cube N} =>
        chiHat (Work.BoseB4.vec (m.val - a)) ^ 2 + chiHat (Work.BoseB4.vec (m.val - c)) ^ 2)
      (fun m => abs_nonneg _) hle (hsum_a.add hsum_c)
  have hmono := Summable.tsum_le_tsum hle hsum_abs (hsum_a.add hsum_c)
  have hsplit : (∑' m : {m : Z3 // m ∉ cube N},
        (chiHat (Work.BoseB4.vec (m.val - a)) ^ 2 + chiHat (Work.BoseB4.vec (m.val - c)) ^ 2))
      = (∑' m : {m : Z3 // m ∉ cube N}, chiHat (Work.BoseB4.vec (m.val - a)) ^ 2)
        + (∑' m : {m : Z3 // m ∉ cube N}, chiHat (Work.BoseB4.vec (m.val - c)) ^ 2) :=
    Summable.tsum_add hsum_a hsum_c
  calc |tsum (fun m : {m : Fin 3 → ℤ // m ∉ Work.BoseRowQ2.cube N} =>
          Work.BoseRowQ2.chiHat (Work.BoseB4.vec (m.val - a))
            * Work.BoseRowQ2.chiHat (Work.BoseB4.vec (m.val - c)))|
      = ‖tsum (fun m : {m : Fin 3 → ℤ // m ∉ Work.BoseRowQ2.cube N} =>
          Work.BoseRowQ2.chiHat (Work.BoseB4.vec (m.val - a))
            * Work.BoseRowQ2.chiHat (Work.BoseB4.vec (m.val - c)))‖ := (Real.norm_eq_abs _).symm
    _ ≤ ∑' m : {m : Z3 // m ∉ cube N},
          ‖chiHat (Work.BoseB4.vec (m.val - a)) * chiHat (Work.BoseB4.vec (m.val - c))‖ :=
        norm_tsum_le_tsum_norm (by simpa only [Real.norm_eq_abs] using hsum_abs)
    _ = ∑' m : {m : Z3 // m ∉ cube N},
          |chiHat (Work.BoseB4.vec (m.val - a)) * chiHat (Work.BoseB4.vec (m.val - c))| := by
        simp only [Real.norm_eq_abs]
    _ ≤ (∑' m : {m : Z3 // m ∉ cube N}, chiHat (Work.BoseB4.vec (m.val - a)) ^ 2)
        + (∑' m : {m : Z3 // m ∉ cube N}, chiHat (Work.BoseB4.vec (m.val - c)) ^ 2) := by
        rw [← hsplit]; exact hmono
    _ ≤ chiTailC / (rad N L) ^ 101 + chiTailC / (rad N L) ^ 101 := add_le_add hsq_a hsq_c
    _ = 2 * chiTailC / (2 * Real.pi * ((N : ℝ) + 1) - L) ^ 101 := by
        show chiTailC / (rad N L) ^ 101 + chiTailC / (rad N L) ^ 101
          = 2 * chiTailC / (rad N L) ^ 101
        rw [← add_div, ← two_mul]

end Work.BoseRowQ2
