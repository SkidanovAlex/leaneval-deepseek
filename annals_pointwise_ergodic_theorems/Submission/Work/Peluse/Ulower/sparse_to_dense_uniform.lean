import Mathlib
import Submission.Work.Peluse.Ulower.sparse_to_dense

/-!
# Uniform-in-`D` sparse-to-dense comparison for Peluse's box norms

The companion file `Submission/Work/Peluse/Ulower/sparse_to_dense.lean` proves the comparison

`C(D,L,F) * ‖F‖^{2^t}_{□^t_{c[D]}(symIcc L)} ≤ ‖F‖^{2^t}_{□^t_{[|c|D]}(symIcc L)}`

for one triple `(D,L,F)` at a time.  What the §5 assembly of the project consumes
(`Work.Peluse.Ulower.chain_bound`, hypothesis `hsd`) is the *uniform* form: for `t ≥ 2` and
`c ≠ 0` a single constant `C` — depending on `t` and `c` only — works for every `D ≥ 1`, every
window `L` and every `1`-bounded function supported in `symIcc L`.

## Proof

This is exactly the proof of `sparse_to_dense` with the existential quantifier moved in front:
the only input that is used, the dilation comparison `dilated_directions_ge`, *is* already uniform
in `D, L, F` (its constant is `m^{-2t}` for `m = |c|`), so nothing is lost.

* `|c| = 1`: the two box-norm powers are literally equal (`boxNormPow_arithIcc_abs_one`), so
  `C = 1` works.
* `|c| ≥ 2`: set `m := |c|`.  For `c = m > 0`, `c[D] = m[D]` and the interval `1[mD]` are in the
  relation of `dilated_directions_ge` with dilation factor `m` and `c₀ = 1`, whose constant is
  independent of `D, L, F`.  For `c < 0`, reflect the function (`boxSumPow_neg`), which turns
  `c[D] = (-m)[D]` into `m[D]`, and use that the interval direction set `1[mD]` is invariant under
  reflecting the function (`boxNormPow_arithIcc_one_reflect`).

## Main result

* `Work.Peluse.Ulower.sparse_to_dense_uniform`
-/

set_option autoImplicit false

namespace Work.Peluse.Ulower

noncomputable section

open Work.Peluse

theorem sparse_to_dense_uniform (t : ℕ) (ht : 2 ≤ t) (c : ℤ) (hc : c ≠ 0) :
    ∃ C : ℝ, 0 < C ∧ ∀ (D : ℕ), 1 ≤ D → ∀ (L : ℕ) (F : ℤ → ℂ),
      (∀ x : ℤ, ‖F x‖ ≤ 1) → (∀ x : ℤ, x ∉ Work.Peluse.symIcc L → F x = 0) →
      C * Work.Peluse.boxNormPow t (fun _ : Fin t => Work.Peluse.arithIcc c D)
          (Work.Peluse.symIcc L) F
        ≤ Work.Peluse.boxNormPow t (fun _ : Fin t => Work.Peluse.arithIcc 1 (c.natAbs * D))
          (Work.Peluse.symIcc L) F := by
  have hm0 : 1 ≤ c.natAbs := Int.natAbs_pos.mpr hc
  rcases eq_or_lt_of_le hm0 with h1 | h2
  · -- `|c| = 1`: the two direction sets give the same box-norm power
    have hm1 : c.natAbs = 1 := h1.symm
    refine ⟨1, one_pos, ?_⟩
    intro D hD L F hF1 hFspan
    rw [one_mul, boxNormPow_arithIcc_abs_one hm1 D (symIcc L) F, hm1, one_mul]
  · -- `|c| ≥ 2`: use the dilation comparison, whose constant is uniform in `D, L, F`
    obtain ⟨C, hC, hP⟩ := Work.Peluse.BoxNormDilation.dilated_directions_ge ht c.natAbs h2
    refine ⟨C, hC, ?_⟩
    intro D hD L F hF1 hFspan
    have hsupp : SupportIn F L := fun x hx => hFspan x (by
      intro hmem
      rw [mem_symIcc_iff] at hmem
      omega)
    rcases lt_trichotomy c 0 with hclt | hceq | hcgt
    · -- `c < 0`: reflect the function, then use the invariance of the interval
      have hneg : (-(((c.natAbs : ℕ) : ℤ))) = c := by
        have hh : ((((-c).natAbs : ℕ) : ℤ)) = -c :=
          Int.natAbs_of_nonneg (by omega)
        rw [Int.natAbs_neg] at hh
        omega
      have hG1 : ∀ x : Int, ‖(fun x : Int => F (-x)) x‖ ≤ 1 := fun x => hF1 (-x)
      have hGsup : SupportIn (fun x : Int => F (-x)) L := by
        intro x hx
        exact hsupp (-x) (by simpa [Int.natAbs_neg] using hx)
      have h := hP 1 D L (fun x : Int => F (-x)) one_ne_zero hD hG1 hGsup
      have hA : boxNormPow t (fun _ : Fin t => arithIcc (((c.natAbs : ℕ) : ℤ) * 1) D)
            (symIcc L) (fun x => F (-x))
          = boxNormPow t (fun _ : Fin t => arithIcc c D) (symIcc L) F := by
        have hb := (boxSumPow_neg t ((c.natAbs : ℕ) : ℤ) D (symIcc L) F).symm
        rw [hneg] at hb
        have hb' : boxSumPow t (fun _ : Fin t => arithIcc (((c.natAbs : ℕ) : ℤ) * 1) D)
              (symIcc L) (fun x => F (-x))
            = boxSumPow t (fun _ : Fin t => arithIcc c D) (symIcc L) F := by
          rw [mul_one]
          exact hb
        exact congrArg (fun z : ℂ => ‖z‖) hb'
      have hB : boxNormPow t (fun _ : Fin t => arithIcc 1 (c.natAbs * D)) (symIcc L)
            (fun x => F (-x))
          = boxNormPow t (fun _ : Fin t => arithIcc 1 (c.natAbs * D)) (symIcc L) F :=
        boxNormPow_arithIcc_one_reflect t (c.natAbs * D) (symIcc L) F
      rw [hA, hB] at h
      exact h
    · exact absurd hceq hc
    · -- `c > 0`: `arithIcc c D = arithIcc |c| D` is compared with the interval `1[|c|D]`
      have hpos : (((c.natAbs : ℕ) : ℤ)) = c := Int.natAbs_of_nonneg hcgt.le
      have h := hP 1 D L F one_ne_zero hD hF1 hsupp
      have hA : boxNormPow t (fun _ : Fin t => arithIcc (((c.natAbs : ℕ) : ℤ) * 1) D)
            (symIcc L) F
          = boxNormPow t (fun _ : Fin t => arithIcc c D) (symIcc L) F := by
        rw [mul_one, hpos]
      rw [hA] at h
      exact h

end

end Work.Peluse.Ulower
