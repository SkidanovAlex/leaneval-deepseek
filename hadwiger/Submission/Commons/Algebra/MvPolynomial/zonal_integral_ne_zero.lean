import Mathlib
import Submission.Commons.Algebra.MvPolynomial.axisInv_homogeneous_structure
import Submission.Commons.Algebra.MvPolynomial.harmonic_part_axisInvariant
import Submission.Commons.Algebra.MvPolynomial.zonal_harmonic_pair_linDep
import Submission.Commons.Algebra.MvPolynomial.zonal_pole_value_ne_zero
import Submission.Commons.Analysis.MeasureTheory.zonal_profile_integral_value

/-!
# Non-vanishing of the zonal integral

For a homogeneous harmonic polynomial `Z` of even degree `2m` in `n ≥ 2` variables whose
difference from the power of a linear form is divisible by the squared norm, the associated
zonal profile `P` (which represents `Z` on the unit sphere as a function of a single
coordinate) has non-vanishing weighted integral `∫ |t| P(t) (1 - t²)^((n-3)/2) dt`.
-/

set_option linter.unusedSimpArgs false
set_option linter.deprecated false
set_option linter.unnecessarySimpa false
set_option linter.style.haveILetI false

open scoped BigOperators
open MvPolynomial

noncomputable section

namespace Commons.Algebra.MvPolynomial

private abbrev Ez (n : ℕ) := EuclideanSpace ℝ (Fin n)

/-- the subtype sum of squares equals `1 - t^2` on the unit sphere -/
private lemma compl_sum_sq {n : ℕ} [NeZero n] (θ : Metric.sphere (0 : Ez n) 1) :
    (∑ i : {i : Fin n // i ≠ (0 : Fin n)}, ((θ : Ez n) i)^2)
      = 1 - ((θ : Ez n) (0 : Fin n))^2 := by
  have hnorm : ‖(θ : Ez n)‖ = 1 := by
    have h := Metric.mem_sphere.mp θ.2
    simpa [dist_eq_norm] using h
  have hsumsq : (∑ i : Fin n, ((θ : Ez n) i)^2) = 1 := by
    have h1 : ‖(θ : Ez n)‖^2 = ∑ i, ((θ : Ez n) i)^2 := by
      rw [PiLp.norm_sq_eq_of_L2]; simp [Real.norm_eq_abs, sq_abs]
    rw [← h1, hnorm]; norm_num
  have h1 : (∑ i : {i : Fin n // i ≠ (0 : Fin n)}, ((θ : Ez n) i)^2)
      = ∑ i ∈ (Finset.univ.erase (0 : Fin n)), ((θ : Ez n) i)^2 :=
    (Finset.sum_subtype (s := Finset.univ.erase (0 : Fin n))
      (fun x => by simp [Finset.mem_erase]) (fun i : Fin n => ((θ : Ez n) i)^2)).symm
  rw [h1]
  have h2 := Finset.add_sum_erase (Finset.univ : Finset (Fin n)) (fun i => ((θ : Ez n) i)^2)
    (Finset.mem_univ (0 : Fin n))
  rw [hsumsq] at h2
  linarith

/-- the pole vector -/
private def pole {n : ℕ} [NeZero n] : Fin n → ℝ := fun j => if j = 0 then 1 else 0

private lemma pole_eq {n : ℕ} [NeZero n] :
    pole (n := n) = (fun j : Fin n => if j = 0 then (1:ℝ) else 0) := rfl

private lemma pole_zero {n : ℕ} [NeZero n] : pole (n := n) 0 = 1 := by
  rw [pole_eq]; simp

private lemma pole_other {n : ℕ} [NeZero n] {i : Fin n} (hi : i ≠ 0) : pole (n := n) i = 0 := by
  rw [pole_eq]; simp [hi]

private lemma eval_pole_zhSq {n : ℕ} [NeZero n] :
    MvPolynomial.eval (pole (n := n)) zh_Sq = 0 := by
  dsimp [zh_Sq]
  rw [map_sum]
  apply Finset.sum_eq_zero
  intro i _
  rw [map_pow, MvPolynomial.eval_X]
  have hi : (i : Fin n) ≠ 0 := i.2
  rw [pole_other hi]; ring

/-- the value of the zonal sum at the pole `e_0` -/
private lemma eval_zh_range_pole {n : ℕ} [NeZero n] {m r : ℕ} (ch : ℕ → ℝ) :
    MvPolynomial.eval (pole (n := n))
      (∑ j ∈ Finset.range (r+1), ch j • zh_zterm (2*m) j)
      = ch 0 := by
  rw [MvPolynomial.eval_sum]
  have hterm : ∀ j, MvPolynomial.eval (pole (n := n)) (ch j • zh_zterm (2*m) j)
      = ch j * (pole (n := n) 0)^(2*m-2*j) * (MvPolynomial.eval (pole (n := n)) zh_Sq)^j := by
    intro j
    simp only [MvPolynomial.smul_eq_C_mul, zh_zterm, MvPolynomial.eval_mul, MvPolynomial.eval_C,
      MvPolynomial.eval_pow, MvPolynomial.eval_X]
    ring
  rw [Finset.sum_congr rfl (fun j _ => hterm j)]
  rw [Finset.sum_eq_single 0]
  · rw [eval_pole_zhSq, pole_zero]
    norm_num
  · intro j _ hj
    rw [eval_pole_zhSq, pole_zero, zero_pow hj]
    ring
  · intro h; exact absurd (Finset.mem_range.mpr (Nat.succ_pos r)) h

theorem zonal_core_zero {n m : ℕ} [NeZero n] (hn : 2 ≤ n)
    (Z R : MvPolynomial (Fin n) ℝ)
    (hZmem : Z ∈ MvPolynomial.homogeneousSubmodule (Fin n) ℝ (2*m))
    (hlapZ : (∑ j : Fin n, MvPolynomial.pderiv j (MvPolynomial.pderiv j Z)) = 0)
    (hRmem : R ∈ MvPolynomial.homogeneousSubmodule (Fin n) ℝ (2*m - 2))
    (hdec : ((MvPolynomial.X (0:Fin n) : MvPolynomial (Fin n) ℝ))^(2*m) = Z +
        (∑ j : Fin n, (MvPolynomial.X j)^2) * R) :
    ∃ P : Polynomial ℝ,
      (∀ θ : Metric.sphere (0 : Ez n) 1,
        MvPolynomial.eval (fun j : Fin n => (θ : Ez n) j) Z =
          Polynomial.eval ((θ : Ez n) (0:Fin n)) P) ∧
      (∫ t : ℝ in Set.Ioo (-1) 1,
          |t| * Polynomial.eval t P *
            (1 - t ^ 2) ^ (((Fintype.card {j : Fin n // j ≠ (0:Fin n)} : ℝ) - 2) / 2)) ≠ 0 := by
  have hk : 2*m/2 = m := Nat.mul_div_cancel_left m (by norm_num)
  have hIP := harmonic_part_axisInvariant Z R hZmem hlapZ hRmem hdec
  rcases axisInv_homogeneous_structure (n := n) (k := 2*m) hn Z hZmem hIP with ⟨c, hc⟩
  let ch : ℕ → ℝ := zh_extc (2*m/2) c
  have hZrange : Z = ∑ j ∈ Finset.range (2*m/2+1), ch j • zh_zterm (2*m) j := by
    rw [hc]
    dsimp [ch]
    simpa only [zh_zterm, zh_Sq] using (zh_fin_sum_range (n := n) (2*m) c)
  let P : Polynomial ℝ := ∑ j ∈ Finset.range (m+1),
      Polynomial.C (ch j) * Polynomial.X^(2*m-2*j) * (1 - Polynomial.X^2)^j
  have hPeval : ∀ t : ℝ, Polynomial.eval t P
      = ∑ j ∈ Finset.range (m+1), ch j * t^(2*m-2*j) * (1-t^2)^j := by
    intro t
    dsimp [P]
    rw [Polynomial.eval_finsetSum]
    apply Finset.sum_congr rfl
    intro j _
    simp only [Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_pow, Polynomial.eval_X,
      Polynomial.eval_sub, Polynomial.eval_one]
  have hrange : Finset.range (2*m/2+1) = Finset.range (m+1) := by rw [hk]
  have hSq : ∀ θ : Metric.sphere (0 : Ez n) 1,
      MvPolynomial.eval (fun j : Fin n => (θ : Ez n) j) zh_Sq
        = 1 - ((θ : Ez n) (0:Fin n))^2 := by
    intro θ
    have h1 : MvPolynomial.eval (fun j : Fin n => (θ : Ez n) j) zh_Sq
        = ∑ i : {i : Fin n // i ≠ (0:Fin n)}, ((θ : Ez n) (i:Fin n))^2 := by
      dsimp [zh_Sq]
      rw [map_sum]
      apply Finset.sum_congr rfl
      intro i _
      rw [map_pow, MvPolynomial.eval_X]
    rw [h1]; exact compl_sum_sq θ
  have hZθ : ∀ θ : Metric.sphere (0 : Ez n) 1,
      MvPolynomial.eval (fun j : Fin n => (θ : Ez n) j) Z
        = ∑ j ∈ Finset.range (m+1), ch j * ((θ : Ez n) (0:Fin n))^(2*m-2*j)
            * (1 - ((θ : Ez n) (0:Fin n))^2)^j := by
    intro θ
    have hsum : ∀ j, MvPolynomial.eval (fun i : Fin n => (θ : Ez n) i) (ch j • zh_zterm (2*m) j)
        = ch j * ((θ : Ez n) (0:Fin n))^(2*m-2*j)
            * (MvPolynomial.eval (fun i : Fin n => (θ : Ez n) i) zh_Sq)^j := by
      intro j
      simp only [MvPolynomial.smul_eq_C_mul, MvPolynomial.eval_mul, MvPolynomial.eval_C,
        MvPolynomial.eval_pow, MvPolynomial.eval_X, zh_zterm]
      ring
    rw [hZrange, MvPolynomial.eval_sum, hrange]
    rw [Finset.sum_congr rfl (fun j _ => hsum j)]
    rw [Finset.sum_congr rfl (fun j _ => by rw [hSq θ])]
  have hrec : ∀ j : ℕ, j < m →
      ch j * (((2 * m - 2 * j : ℕ) : ℝ) * ((2 * m - 2 * j - 1 : ℕ) : ℝ))
        + ch (j + 1) * ((2 * (j + 1) * (n + 2 * (j + 1) - 3) : ℕ) : ℝ) = 0 := by
    intro j hj
    have hj1 : j + 1 ≤ 2*m/2 := by rw [hk]; omega
    have h1 := zh_coeff_lap_zonal_sum (n := n) hn (2*m) ch j hj1
    have hzl : zh_lap (n := n) (∑ jj ∈ Finset.range (2*m/2+1), ch jj • zh_zterm (n := n) (2*m) jj) = 0 := by
      rw [← hZrange]; dsimp [zh_lap]; exact hlapZ
    rw [hzl] at h1
    rw [MvPolynomial.coeff_zero] at h1
    have ha : zh_alpha (2*m) j = (((2*m-2*j:ℕ):ℝ) * ((2*m-2*j-1:ℕ):ℝ)) := by
      rw [zh_alpha, Nat.cast_mul]
    have hb : zh_beta n (2*m) (j+1) = ((2*(j+1)*(n+2*(j+1)-3):ℕ):ℝ) := by
      rw [zh_beta]
    rw [ha, hb] at h1
    exact h1.symm
  have hch0 : ch 0 = MvPolynomial.eval (pole (n:=n)) Z := by
    rw [hZrange]
    exact (eval_zh_range_pole (n := n) (m := m) (r := 2*m/2) ch).symm
  have hji : ∃ j : Fin n, j ≠ (0:Fin n) := by
    refine ⟨⟨1, by omega⟩, ?_⟩
    intro h; have := congrArg (fun i : Fin n => (i:ℕ)) h; simp at this
  have hdec' : ((∑ j : Fin n, (MvPolynomial.C ((EuclideanSpace.single (0:Fin n) (1:ℝ) : Ez n) j)) * (MvPolynomial.X j)))^(2*m)
      = Z + (∑ j : Fin n, (MvPolynomial.X j)^2) * R := by
    rw [zpo_linearForm_eq_X]; exact hdec
  have hZpole : MvPolynomial.eval (pole (n:=n)) Z ≠ 0 := by
    have hh := zonal_pole_value_ne_zero (n := n) (k := 2*m) (i := (0:Fin n)) hji Z R hZmem hlapZ hRmem hdec'
    rw [pole_eq]
    simpa only [EuclideanSpace.single_apply] using hh
  have hch0ne : ch 0 ≠ 0 := by rw [hch0]; exact hZpole
  have hchm : ch m ≠ 0 := by
    have key : ∀ j, j ≤ m → ch j ≠ 0 := by
      intro j
      induction j with
      | zero => intro _; exact hch0ne
      | succ j ih =>
          intro hj
          have hj' : j < m := by omega
          have hrecj := hrec j hj'
          have hα : (((2*m-2*j:ℕ):ℝ) * ((2*m-2*j-1:ℕ):ℝ)) ≠ 0 := by
            apply mul_ne_zero <;> rw [Nat.cast_ne_zero] <;> omega
          have hβ : ((2*(j+1)*(n+2*(j+1)-3):ℕ):ℝ) ≠ 0 := by
            rw [Nat.cast_ne_zero]; apply mul_ne_zero <;> omega
          have hcj : ch j ≠ 0 := ih (by omega)
          have h1 : ch (j+1) * ((2*(j+1)*(n+2*(j+1)-3):ℕ):ℝ)
              = - (ch j * (((2*m-2*j:ℕ):ℝ)*((2*m-2*j-1:ℕ):ℝ))) := by linarith [hrecj]
          intro hc
          rw [hc, zero_mul] at h1
          have h2 : ch j * (((2*m-2*j:ℕ):ℝ)*((2*m-2*j-1:ℕ):ℝ)) = 0 := by linarith [h1]
          exact (mul_ne_zero hcj hα) h2
    exact key m le_rfl
  refine ⟨P, ?_, ?_⟩
  · intro θ
    rw [hZθ θ, hPeval]
  · simp only [hPeval]
    have hcard : Fintype.card {j : Fin n // j ≠ (0:Fin n)} = n - 1 := by
      rw [Fintype.card_subtype_compl (p := fun j : Fin n => j = (0:Fin n)),
        Fintype.card_subtype_eq, Fintype.card_fin]
    have hexp : (((Fintype.card {j : Fin n // j ≠ (0:Fin n)} : ℝ) - 2) / 2) = (((n:ℝ)-3)/2) := by
      rw [hcard]
      have h1 : ((n - 1 : ℕ) : ℝ) = (n:ℝ) - 1 := by
        rw [Nat.cast_sub (by omega : 1 ≤ n)]; norm_num
      rw [h1]; ring
    rw [hexp]
    rw [Commons.Analysis.MeasureTheory.zonal_profile_integral_value n hn m ch hrec]
    apply div_ne_zero
    · exact neg_ne_zero.mpr hchm
    · apply mul_ne_zero
      · rcases Nat.eq_zero_or_pos m with h | h
        · subst h; norm_num
        · have hm1 : (1:ℝ) ≤ (m:ℝ) := by exact_mod_cast h
          intro hh; linarith
      · have hmnn : (0:ℝ) ≤ (m:ℝ) := Nat.cast_nonneg m
        have hn2 : (2:ℝ) ≤ n := by exact_mod_cast hn
        intro hh
        have hpos : (0:ℝ) < ((n:ℝ)-1)/2 := by linarith
        linarith
theorem zonal_integral_ne_zero
    {n : ℕ} {m : ℕ} (i : Fin n) (hn : 2 ≤ n)
    (Z R : MvPolynomial (Fin n) ℝ)
    (hZmem : Z ∈ MvPolynomial.homogeneousSubmodule (Fin n) ℝ (2 * m))
    (hlapZ : (∑ j : Fin n, MvPolynomial.pderiv j (MvPolynomial.pderiv j Z)) = 0)
    (hRmem : R ∈ MvPolynomial.homogeneousSubmodule (Fin n) ℝ (2 * m - 2))
    (hdec : ((∑ j : Fin n, (MvPolynomial.C ((EuclideanSpace.single i (1 : ℝ) : EuclideanSpace ℝ (Fin n)) j)) * (MvPolynomial.X j)) ^ (2 * m)) = Z +
        (∑ j : Fin n, (MvPolynomial.X j)^2) * R) :
    ∃ P : Polynomial ℝ,
      (∀ θ : Metric.sphere (0 : EuclideanSpace ℝ (Fin n)) 1,
        MvPolynomial.eval (fun j : Fin n => (θ : EuclideanSpace ℝ (Fin n)) j) Z =
          Polynomial.eval ((θ : EuclideanSpace ℝ (Fin n)) i) P) ∧
      (∫ t : ℝ in Set.Ioo (-1) 1,
          |t| * Polynomial.eval t P *
            (1 - t ^ 2) ^ (((Fintype.card {j : Fin n // j ≠ i} : ℝ) - 2) / 2)) ≠ 0 := by
  haveI : NeZero n := ⟨by omega⟩
  let σ : Equiv.Perm (Fin n) := Equiv.swap i (0:Fin n)
  have hσi : σ i = (0:Fin n) := by simp [σ]
  have hσ0 : σ (0:Fin n) = i := by simp [σ]
  have hσinv : ∀ k : Fin n, σ (σ k) = k := by
    intro k
    show Equiv.swap i (0:Fin n) (Equiv.swap i (0:Fin n) k) = k
    simp only [Equiv.swap_apply_def]
    by_cases h1 : k = i
    · subst h1; simp
    · by_cases h2 : k = (0:Fin n)
      · subst h2; simp [h1]
      · simp [h1, h2]
  let Z' : MvPolynomial (Fin n) ℝ := MvPolynomial.renameEquiv ℝ σ Z
  let R' : MvPolynomial (Fin n) ℝ := MvPolynomial.renameEquiv ℝ σ R
  have hZ'mem : Z' ∈ MvPolynomial.homogeneousSubmodule (Fin n) ℝ (2*m) := by
    dsimp [Z']; exact rename_mem_homogeneous σ Z hZmem
  have hlapZ' : (∑ j : Fin n, MvPolynomial.pderiv j (MvPolynomial.pderiv j Z')) = 0 := by
    dsimp [Z']; rw [rename_lap σ Z, hlapZ, map_zero]
  have hR'mem : R' ∈ MvPolynomial.homogeneousSubmodule (Fin n) ℝ (2*m - 2) := by
    dsimp [R']; exact rename_mem_homogeneous σ R hRmem
  have hdec2 : ((MvPolynomial.X i : MvPolynomial (Fin n) ℝ))^(2*m)
      = Z + (∑ j : Fin n, (MvPolynomial.X j)^2) * R := by
    rw [← zpo_linearForm_eq_X i]; exact hdec
  have hdec' : ((MvPolynomial.X (0:Fin n) : MvPolynomial (Fin n) ℝ))^(2*m)
      = Z' + (∑ j : Fin n, (MvPolynomial.X j)^2) * R' := by
    have h := congrArg (MvPolynomial.renameEquiv ℝ σ) hdec2
    simp only [map_pow, map_add, map_mul] at h
    rw [MvPolynomial.renameEquiv_apply, MvPolynomial.rename_X, hσi,
      Commons.Algebra.MvPolynomial.rename_X2 n σ] at h
    simpa only [Z', R'] using h
  rcases zonal_core_zero hn Z' R' hZ'mem hlapZ' hR'mem hdec' with ⟨P, hPrad, hPint⟩
  refine ⟨P, ?_, ?_⟩
  · intro θ
    let y : Ez n := WithLp.toLp 2 (fun k : Fin n => (θ : Ez n) (σ k))
    have hycoe : ∀ k : Fin n, (y : Ez n) k = (θ : Ez n) (σ k) := fun k => rfl
    have hynorm : ‖y‖ = 1 := by
      have hsq : ‖y‖^2 = ∑ k : Fin n, ((θ : Ez n) (σ k))^2 := by
        rw [PiLp.norm_sq_eq_of_L2]
        simp only [hycoe, Real.norm_eq_abs, sq_abs]
      have hsum : (∑ k : Fin n, ((θ : Ez n) (σ k))^2) = ∑ k : Fin n, ((θ:Ez n) k)^2 :=
        Equiv.sum_comp σ (fun k => ((θ:Ez n) k)^2)
      have hθsq : (∑ k : Fin n, ((θ:Ez n) k)^2) = 1 := by
        have h1 : ‖(θ:Ez n)‖^2 = ∑ k, ((θ:Ez n) k)^2 := by
          rw [PiLp.norm_sq_eq_of_L2]; simp [Real.norm_eq_abs, sq_abs]
        have h2 : ‖(θ:Ez n)‖ = 1 := by
          have := Metric.mem_sphere.mp θ.2; simpa [dist_eq_norm] using this
        rw [← h1, h2]; norm_num
      have hsq2 : ‖y‖^2 = 1 := by rw [hsq, hsum, hθsq]
      nlinarith [norm_nonneg y, hsq2]
    have hymem : y ∈ Metric.sphere (0 : Ez n) 1 := by
      rw [Metric.mem_sphere, dist_eq_norm]; simpa using hynorm
    have hkey := hPrad ⟨y, hymem⟩
    have hconv : MvPolynomial.eval (fun j : Fin n => (y:Ez n) j) Z'
        = MvPolynomial.eval (fun j : Fin n => (θ:Ez n) j) Z := by
      dsimp [Z']
      rw [MvPolynomial.renameEquiv_apply, MvPolynomial.eval_rename]
      apply congrArg (fun f : Fin n → ℝ => MvPolynomial.eval f Z)
      funext k
      rw [Function.comp_apply, hycoe (σ k), hσinv k]
    rw [← hconv, hkey]
    show Polynomial.eval ((y:Ez n) 0) P = Polynomial.eval ((θ:Ez n) i) P
    rw [hycoe 0, hσ0]
  · have hcardi : Fintype.card {j : Fin n // j ≠ i} = n - 1 := by
      rw [Fintype.card_subtype_compl (p := fun j : Fin n => j = i),
        Fintype.card_subtype_eq, Fintype.card_fin]
    have hcard0 : Fintype.card {j : Fin n // j ≠ (0:Fin n)} = n - 1 := by
      rw [Fintype.card_subtype_compl (p := fun j : Fin n => j = (0:Fin n)),
        Fintype.card_subtype_eq, Fintype.card_fin]
    have hcardij : Fintype.card {j : Fin n // j ≠ i} = Fintype.card {j : Fin n // j ≠ (0:Fin n)} := by
      rw [hcardi, hcard0]
    rw [hcardij]
    exact hPint

end Commons.Algebra.MvPolynomial
