import Mathlib
import Submission.Work.HP.Defs
import Submission.Work.HP.Vero.SigmaDefs
import Submission.Work.HP.Vero.LamAux
import Submission.Work.HP.Vero.dualLat_int_shift
import Submission.Work.HP.Vero.SecondCaseDefs
import Submission.Work.HP.Vero.dmin_three_le_eucDist
import Submission.Work.HP.Vero.second_case_witness
import Submission.Work.HP.Lat.span_pair_lattice
import Submission.Work.HP.Lat.detL_ge_one

namespace Work.HP.Vero

open Work.HP

set_option linter.unusedVariables false

/-! ## Helper: the pairing of `ν₂(z)` with `σ(u,w)` in real form -/

/-- The real form of `dot_veronese_sigma`: `⟨ν₂(z), σ(u,w)⟩ = ⟨z,u⟩⟨z,w⟩`. -/
lemma dot_veronese_sigmaR (n : ℕ) (z u w : Fin (n + 1) → ℤ) :
    (∑ m : Mon 2 n, (toR (veronese 2 n z)) m * (sigma n u w m : ℝ))
      = ((∑ k, z k * u k : ℤ) : ℝ) * ((∑ k, z k * w k : ℤ) : ℝ) := by
  have h := dot_veronese_sigma n z u w
  have hcast : (∑ m : Mon 2 n, (toR (veronese 2 n z)) m * (sigma n u w m : ℝ))
      = ((∑ m : Mon 2 n, veronese 2 n z m * sigma n u w m : ℤ) : ℝ) := by
    push_cast
    exact Finset.sum_congr rfl (fun m _ => rfl)
  rw [hcast, h, Int.cast_mul]

/-- The set of determinants of rank-two lattices through `x` and `y` is nonempty. -/
lemma dmin_pair_nonempty {n : ℕ} (x y : Fin (n + 1) → ℤ) (hxy : LinearIndependent ℤ ![x, y]) :
    ({D : ℝ | ∃ L : Submodule ℤ (Fin (n + 1) → ℤ), rk L = 2 ∧
      ({x, y} : Set (Fin (n + 1) → ℤ)) ⊆ L ∧ detL L = D}).Nonempty := by
  obtain ⟨L0, hrk0, hx0, hy0, -⟩ := Work.HP.Lat.span_pair_lattice x y hxy
  refine ⟨detL L0, L0, hrk0, ?_, rfl⟩
  intro z hz
  rcases hz with h | h
  · rw [h]; exact hx0
  · rw [h]; exact hy0

/-- `0 ≤ 𝔡₂(x,y)`. -/
lemma dmin_nonneg_pair {n : ℕ} (x y : Fin (n + 1) → ℤ) (hxy : LinearIndependent ℤ ![x, y]) :
    0 ≤ dmin 2 ({x, y} : Set (Fin (n + 1) → ℤ)) := by
  unfold dmin
  exact le_csInf (dmin_pair_nonempty x y hxy)
    (by rintro D ⟨L, -, -, rfl⟩; exact detL_nonneg L)

/-- `1 ≤ 𝔡₂(x,y)`: the determinant of a nonzero lattice is at least one. -/
lemma dmin_one_le_pair {n : ℕ} (x y : Fin (n + 1) → ℤ) (hxy : LinearIndependent ℤ ![x, y]) :
    1 ≤ dmin 2 ({x, y} : Set (Fin (n + 1) → ℤ)) := by
  unfold dmin
  exact le_csInf (dmin_pair_nonempty x y hxy)
    (by rintro D ⟨L, -, -, rfl⟩; exact Work.HP.Lat.detL_ge_one L)

/-- The paper's "Lower bound second case" (Browning–Le Boudec–Sawin §3.3, `d = 2`): if a nonzero
element `a` of the dual lattice of `Γ = Λ_{ν₂(x)} ∩ Λ_{ν₂(y)}` does not lie in
`span_ℝ(ν₂x, ν₂y, ν₂(x+y))`, then `rNorm a ≥ 𝔡₃/𝔡₂ = dmin 3 {x,y}/dmin 2 {x,y}`.

Route (paper §3.3).  By `dualLat_int_shift`, write `a = b + t` with `b : Mon 2 n → ℤ` and
`t ∈ span_ℝ(ν₂x, ν₂y)`.  By `second_case_witness` (the identity
`⟨ν₂(z), sigma n u v⟩ = ⟨z,u⟩⟨z,v⟩` plus the dimension count
`span σ(ℤ^{n+1} × ℒ^⊥) = (span Q₃)^⊥`) there are `i` and `v` with `⟨v,x⟩ = ⟨v,y⟩ = 0` and
`⟨a, sigma n (Pi.single i 1) v⟩ ≠ 0`.  That pairing equals `⟨rowVec n i b, v⟩` (`dot_sigma_rowVecR`),
and `rowVec n i b - rowVec n i a` differs from `rowVec n i a` by an element of `span_ℝ{x,y}` because
`b - a = λ·ν₂x + μ·ν₂y` and `rowVec n i (veronese 2 n x) = x i • x` (`rowVecR_veronese`); hence
`rowVec n i b ∉ span_ℝ{x,y}` and `eucDist(rowVec n i b, span_ℝ{x,y}) ≤ rNorm (rowVec n i a) ≤ rNorm a`
(coordinate projection).  Finally `dmin 3 {x,y} ≤ dmin 2 {x,y} · eucDist(w, span_ℝ{x,y})` for any
integer `w ∉ span_ℝ{x,y}` (the lattice `ℒ(x,y) + ℤw`), which is `dmin_three_le_eucDist`. -/
theorem second_case_bound {n : ℕ} (hn : 2 ≤ n) (x y : Fin (n + 1) → ℤ) (hx : IsPrim x)
    (hy : IsPrim y) (hxy : LinearIndependent ℤ ![x, y]) (a : Mon 2 n → ℝ)
    (ha : a ∈ dualLat (realify (Gam 2 n x y)))
    (hspan : a ∉ Submodule.span ℝ {toR (veronese 2 n x), toR (veronese 2 n y),
      toR (veronese 2 n (x + y))}) :
    dmin 3 ({x, y} : Set (Fin (n + 1) → ℤ)) / dmin 2 ({x, y} : Set (Fin (n + 1) → ℤ))
      ≤ rNorm a := by
  classical
  -- Step 1: an integer representative modulo `span_ℝ(ν₂x, ν₂y)`.
  obtain ⟨b, lam, mu, hb⟩ := dualLat_int_shift x y hx hy hxy a ha
  -- Step 2: a witness `(eᵢ, v)` with `v ⊥ x, v ⊥ y` and `⟨a, σ(eᵢ,v)⟩ ≠ 0`.
  obtain ⟨i, v, hvx, hvy, hai⟩ := second_case_witness x y hxy a hspan
  -- The `i`-th row of the shift.
  set w : Fin (n + 1) → ℤ := rowVec n i b with hwdef
  have hwR : toR w = rowVecR n i (toR b) := by
    rw [hwdef]; exact (rowVecR_toR n i b).symm
  -- Step 3: `⟨w, v⟩ ≠ 0`.
  have hpair_wv : (∑ j, (w j : ℝ) * (v j : ℝ))
      = ∑ m : Mon 2 n, (toR b) m * (sigma n (Pi.single i 1) v m : ℝ) := by
    have hA : (∑ j, (w j : ℝ) * (v j : ℝ))
        = ∑ j, rowVecR n i (toR b) j * (v j : ℝ) := by
      refine Finset.sum_congr rfl (fun j _ => ?_)
      exact congrArg (fun t : ℝ => t * (v j : ℝ)) (congrFun hwR j)
    rw [hA]
    exact (dot_sigma_rowVecR n i v (toR b)).symm
  have hBne : (∑ m : Mon 2 n, (toR b) m * (sigma n (Pi.single i 1) v m : ℝ)) ≠ 0 := by
    have hdecomp : (∑ m : Mon 2 n, (toR b) m * (sigma n (Pi.single i 1) v m : ℝ))
        = (∑ m : Mon 2 n, a m * (sigma n (Pi.single i 1) v m : ℝ))
          + ∑ m : Mon 2 n, ((b m : ℝ) - a m) * (sigma n (Pi.single i 1) v m : ℝ) := by
      rw [← Finset.sum_add_distrib]
      refine Finset.sum_congr rfl (fun m _ => ?_)
      show (b m : ℝ) * _ = a m * _ + ((b m : ℝ) - a m) * _
      ring
    have hzero : (∑ m : Mon 2 n, ((b m : ℝ) - a m) * (sigma n (Pi.single i 1) v m : ℝ)) = 0 := by
      have hstep : ∀ m : Mon 2 n, ((b m : ℝ) - a m) * (sigma n (Pi.single i 1) v m : ℝ)
          = lam * ((toR (veronese 2 n x)) m * (sigma n (Pi.single i 1) v m : ℝ))
            + mu * ((toR (veronese 2 n y)) m * (sigma n (Pi.single i 1) v m : ℝ)) := by
        intro m
        rw [hb m, add_mul]
        ring
      rw [Finset.sum_congr rfl (fun m _ => hstep m), Finset.sum_add_distrib]
      have hxsingle : (∑ k : Fin (n + 1), x k * (Pi.single i 1 : Fin (n + 1) → ℤ) k) = x i := by
        rw [Finset.sum_eq_single i]
        · simp
        · intro t _ ht; rw [Pi.single_eq_of_ne ht]; ring
        · intro h; exact absurd (Finset.mem_univ i) h
      have hysingle : (∑ k : Fin (n + 1), y k * (Pi.single i 1 : Fin (n + 1) → ℤ) k) = y i := by
        rw [Finset.sum_eq_single i]
        · simp
        · intro t _ ht; rw [Pi.single_eq_of_ne ht]; ring
        · intro h; exact absurd (Finset.mem_univ i) h
      have hxv : (∑ k : Fin (n + 1), x k * v k) = 0 := by
        rw [← hvx]; exact Finset.sum_congr rfl (fun k _ => mul_comm _ _)
      have hyv : (∑ k : Fin (n + 1), y k * v k) = 0 := by
        rw [← hvy]; exact Finset.sum_congr rfl (fun k _ => mul_comm _ _)
      have hx0 : (∑ m : Mon 2 n, (toR (veronese 2 n x)) m * (sigma n (Pi.single i 1) v m : ℝ))
          = 0 := by
        rw [dot_veronese_sigmaR, hxsingle, hxv, Int.cast_zero, mul_zero]
      have hy0 : (∑ m : Mon 2 n, (toR (veronese 2 n y)) m * (sigma n (Pi.single i 1) v m : ℝ))
          = 0 := by
        rw [dot_veronese_sigmaR, hysingle, hyv, Int.cast_zero, mul_zero]
      have hfacx : (∑ m : Mon 2 n,
          lam * ((toR (veronese 2 n x)) m * (sigma n (Pi.single i 1) v m : ℝ)))
          = lam * (∑ m : Mon 2 n, (toR (veronese 2 n x)) m * (sigma n (Pi.single i 1) v m : ℝ)) :=
        (Finset.mul_sum Finset.univ _ lam).symm
      have hfacy : (∑ m : Mon 2 n,
          mu * ((toR (veronese 2 n y)) m * (sigma n (Pi.single i 1) v m : ℝ)))
          = mu * (∑ m : Mon 2 n, (toR (veronese 2 n y)) m * (sigma n (Pi.single i 1) v m : ℝ)) :=
        (Finset.mul_sum Finset.univ _ mu).symm
      rw [hfacx, hfacy, hx0, hy0, mul_zero, mul_zero, add_zero]
    rw [hdecomp, hzero, add_zero]
    exact hai
  have hpair : (∑ j, (w j : ℝ) * (v j : ℝ)) ≠ 0 := by
    rw [hpair_wv]; exact hBne
  -- Step 4: `w ∉ span_ℝ{x,y}`.
  have hw_notmem : toR w ∉ Submodule.span ℝ ({toR x, toR y} : Set (Fin (n + 1) → ℝ)) := by
    intro hmem
    have h0 : (∑ j, (toR w) j * (v j : ℝ)) = 0 := sum_mul_eq_zero_of_mem_span hvx hvy hmem
    exact hpair h0
  -- Step 5: `toR w - rᵢ(a)` lies in `span_ℝ{x,y}`.
  have hshift : toR w - rowVecR n i a
      = lam • ((x i : ℝ) • toR x) + mu • ((y i : ℝ) • toR y) := by
    funext j
    have h := hb (pairMon n i j)
    show (toR w) j - rowVecR n i a j = _
    rw [congrFun hwR j, rowVecR_apply, rowVecR_apply]
    show (b (pairMon n i j) : ℝ) - a (pairMon n i j) = _
    rw [h]
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, toR, veronese_pairMon]
    push_cast
    ring
  have hzmem : (toR w - rowVecR n i a)
      ∈ Submodule.span ℝ ({toR x, toR y} : Set (Fin (n + 1) → ℝ)) := by
    rw [hshift]
    refine Submodule.add_mem _ ?_ ?_
    · exact Submodule.smul_mem _ lam
        (Submodule.smul_mem _ (x i : ℝ) (Submodule.subset_span (by simp)))
    · exact Submodule.smul_mem _ mu
        (Submodule.smul_mem _ (y i : ℝ) (Submodule.subset_span (by simp)))
  -- Step 6: the Euclidean distance of `w` to `span_ℝ{x,y}` is at most `‖rᵢ(a)‖ ≤ ‖a‖`.
  have heuc : eucDist (toR w) ((Submodule.span ℝ ({toR x, toR y} : Set (Fin (n + 1) → ℝ)) :
      Submodule ℝ (Fin (n + 1) → ℝ)) : Set (Fin (n + 1) → ℝ)) ≤ rNorm a := by
    have h1 := eucDist_le (toR w) ((Submodule.span ℝ ({toR x, toR y} :
      Set (Fin (n + 1) → ℝ))) : Set (Fin (n + 1) → ℝ)) hzmem
    have h2 : rNorm (toR w - (toR w - rowVecR n i a)) = rNorm (rowVecR n i a) := by
      congr 1; abel
    rw [h2] at h1
    exact h1.trans (rNorm_rowVecR_le n i a)
  -- Step 7: the lattice inequality.
  have hdmin3 : dmin 3 ({x, y} : Set (Fin (n + 1) → ℤ))
      ≤ dmin 2 ({x, y} : Set (Fin (n + 1) → ℤ)) * rNorm a := by
    have h := dmin_three_le_eucDist (ι := Fin (n + 1)) x y w hxy hw_notmem
    exact h.trans (mul_le_mul_of_nonneg_left heuc (dmin_nonneg_pair x y hxy))
  -- Step 8: positivity of `𝔡₂` and conclusion.
  have hpos : 0 < dmin 2 ({x, y} : Set (Fin (n + 1) → ℤ)) :=
    lt_of_lt_of_le zero_lt_one (dmin_one_le_pair x y hxy)
  rw [div_le_iff₀ hpos]
  calc dmin 3 ({x, y} : Set (Fin (n + 1) → ℤ))
      ≤ dmin 2 ({x, y} : Set (Fin (n + 1) → ℤ)) * rNorm a := hdmin3
    _ = rNorm a * dmin 2 ({x, y} : Set (Fin (n + 1) → ℤ)) := by ring

end Work.HP.Vero
