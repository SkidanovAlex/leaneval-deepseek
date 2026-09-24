import Mathlib
import Submission.Work.GM.Trace.Defs

open Complex Finset
open scoped BigOperators
set_option autoImplicit false
set_option maxHeartbeats 4000000

namespace Work.GM.Trace

open Submission.GM Submission.LargeValues

/-!
# GM 4.5, identity part: the cubic trace of `M_W`

The matrix `M = M_W` has entries `w(n/N) n^{it}`.  We compute

  `tr((M M*)^3) = Σ_{t₁,t₂,t₃ ∈ W} (M M*)_{t₁t₂} (M M*)_{t₂t₃} (M M*)_{t₃t₁}`

and expand `(M M*)_{ts} = N^{i(t-s)} Σ_{n∈[N,2N]} h_{t-s}(n/N)`.  The three powers of `N`
cancel on the diagonal of the cube, so the trace is a triple sum of the one-dimensional
Poisson sums; `hpoi` is Poisson summation (GM §4) and `hsum` its summability.
-/

/-! ## Pointwise complex-power identities -/

/-- `x^{ia} conj(x^{ib}) = x^{i(a-b)}` for `x > 0`. -/
theorem cpow_mul_star_cpow {x : ℝ} (hx : 0 < x) (a b : ℝ) :
    ((x:ℂ) ^ (Complex.I * (a:ℂ))) * star ((x:ℂ) ^ (Complex.I * (b:ℂ)))
      = (x:ℂ) ^ (Complex.I * ((a - b : ℝ):ℂ)) := by
  have hxne : ((x:ℝ):ℂ) ≠ 0 := by exact_mod_cast hx.ne'
  have hnorm : ‖((x:ℂ) ^ (Complex.I * (b:ℂ)))‖ = 1 := by
    rw [Complex.norm_cpow_eq_rpow_re_of_pos hx]
    simp
  have h2 : star ((x:ℂ) ^ (Complex.I * (b:ℂ))) = (((x:ℂ) ^ (Complex.I * (b:ℂ))))⁻¹ :=
    (Complex.inv_eq_conj hnorm).symm
  rw [h2, ← div_eq_mul_inv, ← Complex.cpow_sub (x := (x:ℂ)) (y := Complex.I*(a:ℂ))
    (z := Complex.I*(b:ℂ)) hxne]
  congr 1
  push_cast
  ring

/-- The entry `(w x^{ia}) · conj(w x^{ib})` of `M_W M_W*`. -/
theorem entry_star (w x : ℝ) (hx : 0 < x) (a b : ℝ) :
    (((w:ℂ) * (x:ℂ)^(Complex.I*(a:ℂ))) * star ((w:ℂ) * (x:ℂ)^(Complex.I*(b:ℂ))))
      = ((w^2:ℝ):ℂ) * (x:ℂ)^(Complex.I*((a-b:ℝ):ℂ)) := by
  have h := cpow_mul_star_cpow hx a b
  have hs : star ((w:ℂ) * (x:ℂ)^(Complex.I*(b:ℂ)))
      = (w:ℂ) * star ((x:ℂ)^(Complex.I*(b:ℂ))) := by
    simp [star_mul, mul_comm, Complex.conj_ofReal]
  rw [hs, ← h]
  have hw : ((w^2:ℝ):ℂ) = (w:ℂ)^2 := by push_cast; ring
  rw [hw]
  ring

/-- The same with a complex base `y` known to be a positive real. -/
theorem entry_star_gen (w : ℝ) (y : ℂ) (r : ℝ) (hr : 0 < r) (hy : y = (r:ℂ)) (a b : ℝ) :
    (((w:ℂ) * y^(Complex.I*(a:ℂ))) * star ((w:ℂ) * y^(Complex.I*(b:ℂ))))
      = ((w^2:ℝ):ℂ) * y^(Complex.I*((a-b:ℝ):ℂ)) := by
  rw [hy]
  exact entry_star w r hr a b

/-- Splitting `n^{ie} = N^{ie} (n/N)^{ie}` for `1 ≤ N`. -/
theorem cpow_split {N : ℕ} (hN : 1 ≤ N) (n : ℕ) (e : ℝ) :
    ((n:ℂ))^(Complex.I*(e:ℂ))
      = (N:ℂ)^(Complex.I*(e:ℂ)) * ((((n:ℝ)/(N:ℝ) : ℝ)):ℂ)^(Complex.I*(e:ℂ)) := by
  have hNpos : (0:ℝ) < (N:ℝ) := by exact_mod_cast hN
  have hbase : (((N:ℝ):ℂ) * ((((n:ℝ)/(N:ℝ) : ℝ)):ℂ)) = (n:ℂ) := by
    have hbaseR : (N:ℝ) * ((n:ℝ)/(N:ℝ)) = (n:ℝ) := mul_div_cancel₀ _ (ne_of_gt hNpos)
    exact_mod_cast hbaseR
  rw [← hbase, Complex.mul_cpow_ofReal_nonneg (a := (N:ℝ)) (b := ((n:ℝ)/(N:ℝ)))
    (le_of_lt hNpos) (by positivity)]
  congr 1

/-- The three powers of `N` cancel on the diagonal of the cube. -/
theorem cpow_N_cancel {N : ℕ} (hN : 1 ≤ N) (t1 t2 t3 : ℝ) :
    (N:ℂ)^(Complex.I*((t1-t2:ℝ):ℂ)) * (N:ℂ)^(Complex.I*((t2-t3:ℝ):ℂ))
      * (N:ℂ)^(Complex.I*((t3-t1:ℝ):ℂ)) = 1 := by
  have hNne : ((N:ℂ)) ≠ 0 := by
    have : (N:ℕ) ≠ 0 := by omega
    exact_mod_cast this
  rw [← Complex.cpow_add _ _ hNne, ← Complex.cpow_add _ _ hNne]
  have : Complex.I * ((t1 - t2 : ℝ) : ℂ) + Complex.I * ((t2 - t3 : ℝ) : ℂ)
      + Complex.I * ((t3 - t1 : ℝ) : ℂ) = 0 := by push_cast; ring
  rw [this, Complex.cpow_zero]

/-! ## The entries of `M_W M_W*` -/

/-- The entry `(M_W M_W*)_{ts}`. -/
theorem MMstar_entry (N : ℕ) (hN : 1 ≤ N) (W : Finset ℝ) (t s : W) (j : Fin (N+1)) :
    MWmat N W t j * (MWmat N W).conjTranspose j s
      = ((bumpW (((((N + (j:ℕ) : ℕ)):ℝ))/(N:ℝ)) ^ 2 : ℝ) : ℂ)
        * ((((N + (j:ℕ)) : ℕ):ℂ)) ^ (Complex.I*(((t:ℝ)-(s:ℝ):ℝ):ℂ)) := by
  rw [Matrix.conjTranspose_apply]
  simp only [MWmat]
  rw [show ((N:ℝ) + ((j:ℕ):ℝ)) = ((((N + (j:ℕ) : ℕ)):ℝ)) by push_cast; ring]
  rw [show ((N:ℂ) + ((j:ℕ):ℂ)) = ((((N + (j:ℕ)) : ℕ):ℂ)) by push_cast; ring]
  exact entry_star_gen (bumpW (((((N + (j:ℕ) : ℕ)):ℝ))/(N:ℝ)))
    ((((N + (j:ℕ)) : ℕ):ℂ)) ((((N + (j:ℕ)) : ℕ):ℝ))
    (by
      have : (1:ℕ) ≤ N + (j:ℕ) := by omega
      exact_mod_cast this)
    (by push_cast; ring) (t:ℝ) (s:ℝ)

/-- `(M_W M_W*)_{ts} = N^{i(t-s)} Σ_{n∈[N,2N]} h_{t-s}(n/N)`. -/
theorem MMstar_apply (N : ℕ) (hN : 1 ≤ N) (W : Finset ℝ) (t s : W) :
    (MWmat N W * (MWmat N W).conjTranspose) t s
      = (N:ℂ)^(Complex.I*(((t:ℝ)-(s:ℝ):ℝ):ℂ))
        * ∑ n ∈ Finset.Icc N (2*N), hfun ((t:ℝ)-(s:ℝ)) ((n:ℝ)/(N:ℝ)) := by
  rw [Matrix.mul_apply]
  rw [Finset.sum_congr rfl (fun j _ => MMstar_entry N hN W t s j)]
  rw [← sum_Icc_eq_sum_fin N (fun n => ((bumpW (((n:ℝ)/(N:ℝ))) ^ 2 : ℝ) : ℂ)
        * (((n:ℂ)) ^ (Complex.I*(((t:ℝ)-(s:ℝ):ℝ):ℂ))))]
  rw [show (∑ n ∈ Finset.Icc N (2*N), ((bumpW ((n:ℝ)/(N:ℝ)) ^ 2 : ℝ) : ℂ)
          * (((n:ℂ)) ^ (Complex.I*(((t:ℝ)-(s:ℝ):ℝ):ℂ))))
      = ∑ n ∈ Finset.Icc N (2*N), (N:ℂ)^(Complex.I*(((t:ℝ)-(s:ℝ):ℝ):ℂ))
          * hfun ((t:ℝ)-(s:ℝ)) ((n:ℝ)/(N:ℝ)) from by
        apply Finset.sum_congr rfl
        intro n _
        rw [cpow_split hN n ((t:ℝ)-(s:ℝ))]
        simp only [hfun]
        ring]
  rw [Finset.mul_sum]

/-! ## The cubic trace -/

/-- Expand the cubic trace into a triple sum over `W`. -/
theorem trace_cube_eq (N : ℕ) (W : Finset ℝ) :
    Matrix.trace ((MWmat N W * (MWmat N W).conjTranspose) ^ 3)
      = ∑ t1 : W, ∑ t2 : W, ∑ t3 : W,
          ((MWmat N W * (MWmat N W).conjTranspose) t1 t2
            * (MWmat N W * (MWmat N W).conjTranspose) t2 t3)
          * (MWmat N W * (MWmat N W).conjTranspose) t3 t1 := by
  have h3 : (MWmat N W * (MWmat N W).conjTranspose) ^ 3
      = ((MWmat N W * (MWmat N W).conjTranspose) * (MWmat N W * (MWmat N W).conjTranspose))
        * (MWmat N W * (MWmat N W).conjTranspose) := by
    rw [show (3:ℕ) = 2 + 1 by norm_num, pow_succ, pow_two]
  have hexp : ∀ t : W,
      (((MWmat N W * (MWmat N W).conjTranspose) * (MWmat N W * (MWmat N W).conjTranspose))
        * (MWmat N W * (MWmat N W).conjTranspose)) t t
      = ∑ c : W, (∑ b : W, (MWmat N W * (MWmat N W).conjTranspose) t b
            * (MWmat N W * (MWmat N W).conjTranspose) b c)
          * (MWmat N W * (MWmat N W).conjTranspose) c t := by
    intro t
    rw [Matrix.mul_apply]
    apply Finset.sum_congr rfl
    intro c _
    rw [Matrix.mul_apply]
  rw [h3]
  show (∑ t : W, (((MWmat N W * (MWmat N W).conjTranspose)
        * (MWmat N W * (MWmat N W).conjTranspose))
        * (MWmat N W * (MWmat N W).conjTranspose)) t t) = _
  simp only [hexp]
  simp only [Finset.sum_mul]
  refine Finset.sum_congr rfl (fun t _ => ?_)
  rw [Finset.sum_comm]

/-- `((x a)(y b))(z c) = (a b) c` when `x y z = 1`. -/
theorem triple_cancel (x y z a b c : ℂ) (h : x*y*z = 1) :
    ((x*a)*(y*b))*(z*c) = (a*b)*c := by
  have hh : ((x*a)*(y*b))*(z*c) = ((a*b)*c) * (x*y*z) := by ring
  rw [hh, h, mul_one]

/-- The cubic trace with the `N`-powers cancelled: a triple sum of products of the
one-dimensional Poisson sums `Σ_n h_{t-s}(n/N)`. -/
theorem trace_cube_reduced (N : ℕ) (hN : 1 ≤ N) (W : Finset ℝ) :
    Matrix.trace ((MWmat N W * (MWmat N W).conjTranspose) ^ 3)
      = ∑ t1 : W, ∑ t2 : W, ∑ t3 : W,
          ((∑ n ∈ Finset.Icc N (2*N), hfun ((t1:ℝ)-(t2:ℝ)) ((n:ℝ)/(N:ℝ)))
           * (∑ n ∈ Finset.Icc N (2*N), hfun ((t2:ℝ)-(t3:ℝ)) ((n:ℝ)/(N:ℝ))))
          * (∑ n ∈ Finset.Icc N (2*N), hfun ((t3:ℝ)-(t1:ℝ)) ((n:ℝ)/(N:ℝ))) := by
  classical
  rw [trace_cube_eq]
  apply Finset.sum_congr rfl; intro t1 _
  apply Finset.sum_congr rfl; intro t2 _
  apply Finset.sum_congr rfl; intro t3 _
  rw [MMstar_apply N hN W t1 t2, MMstar_apply N hN W t2 t3, MMstar_apply N hN W t3 t1]
  exact triple_cancel _ _ _ _ _ _ (cpow_N_cancel hN (t1:ℝ) (t2:ℝ) (t3:ℝ))


/-! ## Sums over `W : Finset ℝ` versus sums over the subtype -/

theorem sum_subtype_eq3 (W : Finset ℝ) (G : ℝ → ℝ → ℝ → ℂ) :
    (∑ t1 : W, ∑ t2 : W, ∑ t3 : W, G (t1:ℝ) (t2:ℝ) (t3:ℝ))
      = ∑ t1 ∈ W, ∑ t2 ∈ W, ∑ t3 ∈ W, G t1 t2 t3 := by
  rw [← Finset.sum_attach W (fun t1 : ℝ => ∑ t2 ∈ W, ∑ t3 ∈ W, G t1 t2 t3)]
  apply Finset.sum_congr rfl
  intro t1 _
  rw [← Finset.sum_attach W (fun t2 : ℝ => ∑ t3 ∈ W, G (t1:ℝ) t2 t3)]
  apply Finset.sum_congr rfl
  intro t2 _
  exact Finset.sum_attach W (fun t3 : ℝ => G (t1:ℝ) (t2:ℝ) t3)

/-- Pull a constant out of three nested finite sums over `W`. -/
theorem mul_out_sum3 (W : Finset ℝ) (a : ℂ) (G : ℝ → ℝ → ℝ → ℂ) :
    (∑ t1 ∈ W, ∑ t2 ∈ W, ∑ t3 ∈ W, a * G t1 t2 t3)
      = a * ∑ t1 ∈ W, ∑ t2 ∈ W, ∑ t3 ∈ W, G t1 t2 t3 := by
  rw [Finset.sum_congr rfl (fun t1 _ => Finset.sum_congr rfl (fun t2 _ =>
    (Finset.mul_sum W (fun t3 : ℝ => G t1 t2 t3) a).symm))]
  rw [Finset.sum_congr rfl (fun t1 _ =>
    (Finset.mul_sum W (fun t2 : ℝ => ∑ t3 ∈ W, G t1 t2 t3) a).symm)]
  exact (Finset.mul_sum W (fun t1 : ℝ => ∑ t2 ∈ W, ∑ t3 ∈ W, G t1 t2 t3) a).symm

/-! ## Products of three `tsum`s over `ℤ` -/

theorem tsum_triple_prod {f g h : ℤ → ℂ}
    (hf : Summable (fun m : ℤ => ‖f m‖)) (hg : Summable (fun m : ℤ => ‖g m‖))
    (hh : Summable (fun m : ℤ => ‖h m‖)) :
    ((∑' m : ℤ, f m) * (∑' m : ℤ, g m)) * (∑' m : ℤ, h m)
      = ∑' m : ℤ × ℤ × ℤ, f m.1 * g m.2.1 * h m.2.2 := by
  have h23 : (∑' m : ℤ, g m) * (∑' m : ℤ, h m) = ∑' p : ℤ × ℤ, g p.1 * h p.2 :=
    tsum_mul_tsum_of_summable_norm hg hh
  have hs23 : Summable (fun p : ℤ × ℤ => ‖g p.1 * h p.2‖) :=
    (summable_mul_of_summable_norm hg hh).norm
  have h123 : (∑' m : ℤ, f m) * (∑' p : ℤ × ℤ, g p.1 * h p.2)
      = ∑' q : ℤ × (ℤ × ℤ), f q.1 * (g q.2.1 * h q.2.2) :=
    tsum_mul_tsum_of_summable_norm hf hs23
  rw [mul_assoc, h23, h123]
  apply tsum_congr
  intro m
  ring

/-! ## Interchanging the finite sums over `W` with the `tsum` over `ℤ³` -/

theorem tsum_fin_swap {ι : Type*} (W : Finset ℝ) (F : ℝ → ℝ → ℝ → ι → ℂ)
    (hF : ∀ t1 ∈ W, ∀ t2 ∈ W, ∀ t3 ∈ W, Summable (F t1 t2 t3)) :
    (∑ t1 ∈ W, ∑ t2 ∈ W, ∑ t3 ∈ W, ∑' m, F t1 t2 t3 m)
      = ∑' m, ∑ t1 ∈ W, ∑ t2 ∈ W, ∑ t3 ∈ W, F t1 t2 t3 m := by
  have h1 : ∀ t1 ∈ W, ∀ t2 ∈ W, Summable (fun m => ∑ t3 ∈ W, F t1 t2 t3 m) :=
    fun t1 ht1 t2 ht2 => summable_sum (fun t3 ht3 => hF t1 ht1 t2 ht2 t3 ht3)
  have h2 : ∀ t1 ∈ W, Summable (fun m => ∑ t2 ∈ W, ∑ t3 ∈ W, F t1 t2 t3 m) :=
    fun t1 ht1 => summable_sum (fun t2 ht2 => h1 t1 ht1 t2 ht2)
  calc ∑ t1 ∈ W, ∑ t2 ∈ W, ∑ t3 ∈ W, ∑' m, F t1 t2 t3 m
      = ∑ t1 ∈ W, ∑ t2 ∈ W, ∑' m, ∑ t3 ∈ W, F t1 t2 t3 m := by
        apply Finset.sum_congr rfl; intro t1 ht1
        apply Finset.sum_congr rfl; intro t2 ht2
        exact (Summable.tsum_finsetSum (s := W) (f := fun t3 m => F t1 t2 t3 m)
          (fun t3 ht3 => hF t1 ht1 t2 ht2 t3 ht3)).symm
    _ = ∑ t1 ∈ W, ∑' m, ∑ t2 ∈ W, ∑ t3 ∈ W, F t1 t2 t3 m := by
        apply Finset.sum_congr rfl; intro t1 ht1
        exact (Summable.tsum_finsetSum (s := W) (f := fun t2 m => ∑ t3 ∈ W, F t1 t2 t3 m)
          (fun t2 ht2 => h1 t1 ht1 t2 ht2)).symm
    _ = ∑' m, ∑ t1 ∈ W, ∑ t2 ∈ W, ∑ t3 ∈ W, F t1 t2 t3 m :=
        (Summable.tsum_finsetSum (s := W) (f := fun t1 m => ∑ t2 ∈ W, ∑ t3 ∈ W, F t1 t2 t3 m)
          (fun t1 ht1 => h2 t1 ht1)).symm

/-! ## Summability of the triple products -/

theorem summable_triple (N : ℕ)
    (hsum : ∀ t : ℝ, Summable (fun m : ℤ => hhat t ((m:ℝ) * (N:ℝ))))
    (t1 t2 t3 : ℝ) :
    Summable (fun m : ℤ × ℤ × ℤ =>
      hhat (t1-t2) ((m.1:ℝ) * (N:ℝ)) * hhat (t2-t3) ((m.2.1:ℝ) * (N:ℝ))
        * hhat (t3-t1) ((m.2.2:ℝ) * (N:ℝ))) := by
  have hf : Summable (fun m : ℤ => ‖hhat (t1-t2) ((m:ℝ) * (N:ℝ))‖) := (hsum (t1-t2)).norm
  have hg : Summable (fun m : ℤ => ‖hhat (t2-t3) ((m:ℝ) * (N:ℝ))‖) := (hsum (t2-t3)).norm
  have hh : Summable (fun m : ℤ => ‖hhat (t3-t1) ((m:ℝ) * (N:ℝ))‖) := (hsum (t3-t1)).norm
  have h23 : Summable (fun p : ℤ × ℤ =>
      hhat (t2-t3) ((p.1:ℝ) * (N:ℝ)) * hhat (t3-t1) ((p.2:ℝ) * (N:ℝ))) :=
    summable_mul_of_summable_norm hg hh
  have h123 := summable_mul_of_summable_norm hf h23.norm
  refine h123.congr (fun q => ?_)
  ring

/-! ## Assembling the trace as `N³ * Σ {}` -/

theorem trace_eq_tsum_prod (N : ℕ) (hN : 1 ≤ N) (W : Finset ℝ)
    (hpoi : ∀ t : ℝ, ∑ n ∈ Finset.Icc N (2 * N), hfun t ((n : ℝ) / (N : ℝ))
        = (N : ℂ) * ∑' m : ℤ, hhat t ((m : ℝ) * (N : ℝ))) :
    Matrix.trace ((MWmat N W * (MWmat N W).conjTranspose) ^ 3)
      = (N:ℂ)^3 * ∑ t1 ∈ W, ∑ t2 ∈ W, ∑ t3 ∈ W,
          ((∑' m : ℤ, hhat (t1-t2) ((m:ℝ)*(N:ℝ)))
            * (∑' m : ℤ, hhat (t2-t3) ((m:ℝ)*(N:ℝ))))
          * (∑' m : ℤ, hhat (t3-t1) ((m:ℝ)*(N:ℝ))) := by
  have key : ∀ t1 t2 t3 : ℝ,
      ((∑ n ∈ Finset.Icc N (2*N), hfun (t1-t2) ((n:ℝ)/(N:ℝ)))
       * (∑ n ∈ Finset.Icc N (2*N), hfun (t2-t3) ((n:ℝ)/(N:ℝ))))
      * (∑ n ∈ Finset.Icc N (2*N), hfun (t3-t1) ((n:ℝ)/(N:ℝ)))
      = (N:ℂ)^3 * (((∑' m : ℤ, hhat (t1-t2) ((m:ℝ)*(N:ℝ)))
            * (∑' m : ℤ, hhat (t2-t3) ((m:ℝ)*(N:ℝ))))
           * (∑' m : ℤ, hhat (t3-t1) ((m:ℝ)*(N:ℝ)))) := by
    intro t1 t2 t3
    rw [hpoi (t1-t2), hpoi (t2-t3), hpoi (t3-t1)]
    ring
  rw [trace_cube_reduced N hN W]
  rw [sum_subtype_eq3 W (fun t1 t2 t3 =>
      ((∑ n ∈ Finset.Icc N (2*N), hfun (t1-t2) ((n:ℝ)/(N:ℝ)))
       * (∑ n ∈ Finset.Icc N (2*N), hfun (t2-t3) ((n:ℝ)/(N:ℝ))))
      * (∑ n ∈ Finset.Icc N (2*N), hfun (t3-t1) ((n:ℝ)/(N:ℝ))))]
  simp only [key]
  rw [mul_out_sum3 W ((N:ℂ)^3) (fun t1 t2 t3 =>
      ((∑' m : ℤ, hhat (t1-t2) ((m:ℝ)*(N:ℝ)))
        * (∑' m : ℤ, hhat (t2-t3) ((m:ℝ)*(N:ℝ))))
       * (∑' m : ℤ, hhat (t3-t1) ((m:ℝ)*(N:ℝ))))]

theorem trace_three_identity (N : ℕ) (hN : 1 ≤ N) (W : Finset ℝ)
    (hpoi : ∀ t : ℝ, ∑ n ∈ Finset.Icc N (2 * N), Submission.GM.hfun t ((n : ℝ) / (N : ℝ))
        = (N : ℂ) * ∑' m : ℤ, Submission.GM.hhat t ((m : ℝ) * (N : ℝ)))
    (hsum : ∀ t : ℝ, Summable (fun m : ℤ => Submission.GM.hhat t ((m : ℝ) * (N : ℝ)))) :
    Matrix.trace ((Submission.LargeValues.MWmat N W *
        (Submission.LargeValues.MWmat N W).conjTranspose) ^ 3)
      = ∑' m : ℤ × ℤ × ℤ, Submission.GM.Iterm N W m := by
  have htriple : ∀ t1 t2 t3 : ℝ,
      ((∑' m : ℤ, hhat (t1-t2) ((m:ℝ)*(N:ℝ)))
        * (∑' m : ℤ, hhat (t2-t3) ((m:ℝ)*(N:ℝ))))
      * (∑' m : ℤ, hhat (t3-t1) ((m:ℝ)*(N:ℝ)))
      = ∑' m : ℤ × ℤ × ℤ, hhat (t1-t2) ((m.1:ℝ)*(N:ℝ))
          * hhat (t2-t3) ((m.2.1:ℝ)*(N:ℝ)) * hhat (t3-t1) ((m.2.2:ℝ)*(N:ℝ)) :=
    fun t1 t2 t3 => tsum_triple_prod (hsum (t1-t2)).norm (hsum (t2-t3)).norm (hsum (t3-t1)).norm
  rw [trace_eq_tsum_prod N hN W hpoi]
  simp only [htriple]
  rw [tsum_fin_swap W (fun t1 t2 t3 (m : ℤ × ℤ × ℤ) =>
        hhat (t1-t2) ((m.1:ℝ)*(N:ℝ)) * hhat (t2-t3) ((m.2.1:ℝ)*(N:ℝ))
          * hhat (t3-t1) ((m.2.2:ℝ)*(N:ℝ)))
      (fun t1 _ t2 _ t3 _ => summable_triple N hsum t1 t2 t3)]
  rw [← tsum_mul_left]
  rfl

end Work.GM.Trace
