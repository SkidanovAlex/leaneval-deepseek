import Mathlib
import Submission.Work.BW.DefsAC
import Submission.Work.BW.num19_half
import Submission.Work.BW.num_T
import Submission.Work.BW.num_D_lower
import Submission.Work.BW.num_xi
import Submission.Work.BW.acH_lower
import Submission.Work.BW.bprod_real_le
import Submission.Work.BW.sigma_ge
import Submission.Work.BW.bprod_ratio24
import Submission.Work.BW.est18
import Submission.Work.BW.est22
import Submission.Work.BW.extrap_core
import Submission.Work.BW.est_f_ge_half_g
import Submission.Work.BW.differentiable_fAt
import Submission.Work.BW.half_num_J
import Submission.Work.BW.half_num_I

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

set_option maxHeartbeats 8000000

open Complex
namespace Work.BW

private lemma pxi_nonneg_h (r : ℕ) : 0 ≤ pxi r := by
  rcases Nat.eq_zero_or_pos r with h | h
  · subst h; simp [pxi]
  · have h1 : (1:ℝ) ≤ (r:ℝ) := by exact_mod_cast h
    simp only [pxi]
    rw [sub_nonneg, div_le_one (by linarith : (0:ℝ) < (r:ℝ))]
    linarith

private lemma pxi_pos_h {r : ℕ} (hr : 2 ≤ r) : 0 < pxi r := by
  have h1 : (2:ℝ) ≤ (r:ℝ) := by exact_mod_cast hr
  have h3 : (0:ℝ) < (r:ℝ) := by linarith
  simp only [pxi]
  rw [sub_pos, div_lt_one h3]
  linarith

private lemma pxi_le_one_h (r : ℕ) : pxi r ≤ 1 := by
  have h : 0 ≤ (0.536:ℝ) / (r:ℝ) := by positivity
  simp only [pxi]; linarith

private lemma SJ_eq (K : Type*) [Field K] [NumberField K] {n : ℕ} (r : ℕ) (b : Fin n → ℤ)
    (v J : ℕ) : SJ K r b v J = ((pxi r ^ r)⁻¹)^J * acS K r b v := by
  rw [SJ, show pxi r ^ (-((r * J : ℕ) : ℤ)) = ((pxi r ^ r)⁻¹)^J by
    rw [zpow_neg, zpow_natCast, pow_mul, inv_pow]]

private lemma TJ_eq (K : Type*) [Field K] [NumberField K] {r : ℕ} (σ : Fin r → ℝ) (J : ℕ) :
    TJ K σ J = (pxi r ^ r)^J * acT K σ := by
  rw [TJ, pow_mul]

/-- `|B(x;X)|^{Tp+1}` bound (BW (23)) allowing `|x| ≤ X+1`. -/
private lemma one_div_sq_le_exp3 (X : ℕ) (hX : 1 ≤ X) :
    (1 + 1/(X:ℝ)) ^ (2*X+1) ≤ Real.exp 3 := by
  have hX1 : (1:ℝ) ≤ (X:ℝ) := by exact_mod_cast hX
  have hX0 : (0:ℝ) < (X:ℝ) := by linarith
  have h1 : (1 + 1/(X:ℝ)) ≤ Real.exp (1/(X:ℝ)) := by
    have := Real.add_one_le_exp (1/(X:ℝ)); linarith
  calc (1 + 1/(X:ℝ)) ^ (2*X+1) ≤ (Real.exp (1/(X:ℝ))) ^ (2*X+1) :=
        pow_le_pow_left₀ (by positivity) h1 _
    _ = Real.exp (((2*X+1 : ℕ) : ℝ) * (1/(X:ℝ))) := by rw [← Real.exp_nat_mul]
    _ ≤ Real.exp 3 := by
        apply Real.exp_le_exp.mpr
        have hm : (((2*X+1 : ℕ)) : ℝ) = 2*(X:ℝ)+1 := by push_cast; ring
        rw [hm, show (2*(X:ℝ)+1) * (1/(X:ℝ)) = (2*(X:ℝ)+1)/(X:ℝ) by ring]
        rw [div_le_iff₀ hX0]
        nlinarith

private lemma bprod_pow_le_exp' (X Tp : ℕ) (x : ℝ) (hX : 1 ≤ X) (hx : |x| ≤ (X : ℝ) + 1) :
    ‖(bprod (7.2 * (X : ℝ)) X x) ^ (Tp + 1)‖ ≤
      Real.exp (-((2 * (X : ℝ) + 1) * ((Tp : ℝ) + 1) * Real.log 7.2) + 3 * ((Tp : ℝ) + 1)) := by
  have hX1 : (1:ℝ) ≤ (X:ℝ) := by exact_mod_cast hX
  have hX0 : (0:ℝ) < (X:ℝ) := by linarith
  have hR : (0:ℝ) < 7.2 * (X:ℝ) := by positivity
  have hX1' : (X:ℝ) + 1 ≤ 7.2 * (X:ℝ) := by nlinarith
  have hxR : |x| ≤ 7.2 * (X:ℝ) := le_trans hx hX1'
  have hb := (bprod_real_le (7.2 * (X:ℝ)) X (by nlinarith) x hxR).1
  have hmax : max |x| (X:ℝ) ≤ (X:ℝ) + 1 := max_le hx (by linarith)
  have hratio : max |x| (X:ℝ) / (7.2 * (X:ℝ)) ≤ (1 + 1/(X:ℝ)) / 7.2 := by
    rw [div_le_div_iff₀ hR (by norm_num : (0:ℝ) < 7.2)]
    have h : (1 + 1/(X:ℝ)) * (7.2 * (X:ℝ)) = 7.2 * ((X:ℝ) + 1) := by
      calc (1 + 1/(X:ℝ)) * (7.2 * (X:ℝ)) = (1 + 1/(X:ℝ)) * 7.2 * (X:ℝ) := by ring
        _ = (7.2 + 7.2/(X:ℝ)) * (X:ℝ) := by ring
        _ = 7.2 * (X:ℝ) + 7.2/(X:ℝ) * (X:ℝ) := by ring
        _ = 7.2 * (X:ℝ) + 7.2 := by rw [div_mul_cancel₀ _ hX0.ne']
        _ = 7.2 * ((X:ℝ) + 1) := by ring
    rw [h]; nlinarith [hmax]
  have hstep1 := one_div_sq_le_exp3 X hX
  have hlog : Real.log ((1 + 1/(X:ℝ))/7.2) ≤ (1/(X:ℝ)) - Real.log 7.2 := by
    rw [Real.log_div (x := 1 + 1/(X:ℝ)) (y := 7.2) (by positivity) (by norm_num)]
    have hp := Real.log_le_sub_one_of_pos (show (0:ℝ) < 1 + 1/(X:ℝ) by positivity)
    linarith
  have hqpos : (0:ℝ) < (1 + 1/(X:ℝ))/7.2 := by positivity
  have hmain : ((1 + 1/(X:ℝ))/7.2) ^ ((2*X+1)*(Tp+1)) ≤
      Real.exp (-((2*(X:ℝ)+1) * ((Tp:ℝ)+1) * Real.log 7.2) + 3*((Tp:ℝ)+1)) := by
    have hm : ((((2*X+1)*(Tp+1) : ℕ)) : ℝ) = (2*(X:ℝ)+1)*((Tp:ℝ)+1) := by push_cast; ring
    have hTp0 : (0:ℝ) ≤ ((Tp:ℝ)+1) := by positivity
    calc ((1 + 1/(X:ℝ))/7.2) ^ ((2*X+1)*(Tp+1))
        = (Real.exp (Real.log ((1 + 1/(X:ℝ))/7.2))) ^ ((2*X+1)*(Tp+1)) := by
          rw [Real.exp_log hqpos]
      _ = Real.exp ((((2*X+1)*(Tp+1) : ℕ) : ℝ) * Real.log ((1 + 1/(X:ℝ))/7.2)) := by
          rw [← Real.exp_nat_mul]
      _ ≤ Real.exp (-((2*(X:ℝ)+1) * ((Tp:ℝ)+1) * Real.log 7.2) + 3*((Tp:ℝ)+1)) := by
          apply Real.exp_le_exp.mpr
          rw [hm]
          have hml : (2*(X:ℝ)+1)*((Tp:ℝ)+1) * (1/(X:ℝ)) ≤ 3*((Tp:ℝ)+1) := by
            rw [show (2*(X:ℝ)+1)*((Tp:ℝ)+1) * (1/(X:ℝ))
                = (2*(X:ℝ)+1)*((Tp:ℝ)+1) / (X:ℝ) by ring]
            rw [div_le_iff₀ hX0]
            nlinarith
          nlinarith [mul_le_mul_of_nonneg_left hlog
            (by positivity : (0:ℝ) ≤ (2*(X:ℝ)+1)*((Tp:ℝ)+1)), hml]
  calc ‖(bprod (7.2 * (X:ℝ)) X x) ^ (Tp + 1)‖
      = ‖bprod (7.2 * (X:ℝ)) X x‖ ^ (Tp + 1) := by rw [norm_pow]
    _ ≤ ((max |x| (X:ℝ) / (7.2 * (X:ℝ))) ^ (2*X+1)) ^ (Tp+1) :=
        pow_le_pow_left₀ (by positivity) hb _
    _ = (max |x| (X:ℝ) / (7.2 * (X:ℝ))) ^ ((2*X+1)*(Tp+1)) := by rw [pow_mul]
    _ ≤ ((1 + 1/(X:ℝ))/7.2) ^ ((2*X+1)*(Tp+1)) :=
        pow_le_pow_left₀ (by positivity) hratio _
    _ ≤ _ := hmain

/-- (24) in the power form, allowing `|x| ≤ X+1`. -/
private lemma bprod_ratio_pow_le' (X Tp : ℕ) (x : ℝ) (z : ℂ) (l : ℤ) (η : ℝ)
    (hX : 1 ≤ X) (hη : 0 < η) (hη' : η < 1/2) (hx : |x| ≤ (X:ℝ) + 1)
    (hl : |l| ≤ (X:ℤ)) (hz : ‖z - (l:ℂ)‖ = η) :
    ‖(bprod (7.2*(X:ℝ)) X x)^(Tp+1)‖ ≤ ‖(bprod (7.2*(X:ℝ)) X z)^(Tp+1)‖ *
      Real.exp (((Tp:ℝ)+1) * (Real.log ((2*Real.pi*η)⁻¹ * (1-η)⁻¹^2 * (X:ℝ)^2 *
        Real.exp (2*(X:ℝ))) + 3)) := by
  set C : ℝ := (2*Real.pi*η)⁻¹ * (1-η)⁻¹^2 * (X:ℝ)^2 * Real.exp (2*(X:ℝ)) with hC
  have hX1 : (1:ℝ) ≤ (X:ℝ) := by exact_mod_cast hX
  have hX0 : (0:ℝ) < (X:ℝ) := by linarith
  have h1η : (0:ℝ) < 1 - η := by linarith [hη']
  have hR : (0:ℝ) < 7.2*(X:ℝ) := by positivity
  have hXR : (X:ℝ) + η ≤ 7.2*(X:ℝ) := by nlinarith
  have hxR : |x| ≤ 7.2*(X:ℝ) := by nlinarith
  have hb := bprod_ratio24 (7.2*(X:ℝ)) η hη hη' X hX hXR l hl z hz x hxR
  have hCpos : 0 < C := by rw [hC]; positivity
  have hmaxle : (max 1 (|x|/(X:ℝ)))^(2*X+1) ≤ Real.exp 3 := by
    have hxle : |x|/(X:ℝ) ≤ 1 + 1/(X:ℝ) := by
      rw [div_le_iff₀ hX0]
      have h : (1 + 1/(X:ℝ)) * (X:ℝ) = (X:ℝ) + 1 := by
        calc (1 + 1/(X:ℝ)) * (X:ℝ) = (X:ℝ) + 1/(X:ℝ) * (X:ℝ) := by ring
          _ = (X:ℝ) + 1 := by rw [div_mul_cancel₀ _ hX0.ne']
      rw [h]; linarith
    have hmax : max 1 (|x|/(X:ℝ)) ≤ 1 + 1/(X:ℝ) := by
      have h1 : (1:ℝ) ≤ 1 + 1/(X:ℝ) := by
        have : (0:ℝ) ≤ 1/(X:ℝ) := by positivity
        linarith
      exact max_le h1 hxle
    calc (max 1 (|x|/(X:ℝ)))^(2*X+1) ≤ (1 + 1/(X:ℝ))^(2*X+1) :=
          pow_le_pow_left₀ (by positivity) hmax _
      _ ≤ Real.exp 3 := one_div_sq_le_exp3 X hX
  have hone : (1:ℝ) ≤ (2*Real.pi*η)⁻¹ * (1-η)⁻¹^2 * (X:ℝ)^2 * Real.exp (2*(X:ℝ)) := by
    have hA : (1:ℝ)/4 ≤ (2*Real.pi*η)⁻¹ := by
      have hq : (2*Real.pi*η) ≤ 4 := by nlinarith [Real.pi_lt_four, hη', Real.pi_pos]
      have := one_div_le_one_div_of_le (by positivity : (0:ℝ) < 2*Real.pi*η) hq
      simpa only [one_div] using this
    have hB : (1:ℝ) ≤ (1-η)⁻¹^2 := by
      have h : (1:ℝ) ≤ (1-η)⁻¹ := by rw [one_le_inv₀ h1η]; linarith [hη]
      nlinarith
    have hX2 : (1:ℝ) ≤ (X:ℝ)^2 := by nlinarith
    have hE : (4:ℝ) ≤ Real.exp (2*(X:ℝ)) := by
      have h2 : (2:ℝ) ≤ 2*(X:ℝ) := by linarith
      have he : (4:ℝ) ≤ Real.exp 2 := by
        have h3 : (2:ℝ) ≤ Real.exp 1 := by
          have := Real.add_one_le_exp (1:ℝ); linarith
        calc (4:ℝ) = 2*2 := by norm_num
          _ ≤ Real.exp 1 * Real.exp 1 := mul_le_mul h3 h3 (by norm_num) (by positivity)
          _ = Real.exp 2 := by rw [← Real.exp_add]; norm_num
      linarith only [Real.exp_le_exp.mpr h2, he]
    calc (1:ℝ) = (1/4) * 1 * 1 * 4 := by norm_num
      _ ≤ (2*Real.pi*η)⁻¹ * (1-η)⁻¹^2 * (X:ℝ)^2 * Real.exp (2*(X:ℝ)) := by
          gcongr
  have hstep : ‖bprod (7.2*(X:ℝ)) X x‖ ≤ ‖bprod (7.2*(X:ℝ)) X z‖ * (C * Real.exp 3) := by
    have hgoal : (2*Real.pi*η)⁻¹ * (1-η)⁻¹^2 * (X:ℝ)^2 * Real.exp (2*(X:ℝ)) *
          (max 1 (|x|/(X:ℝ)))^(2*X+1)
        ≤ (2*Real.pi*η)⁻¹ * (1-η)⁻¹^2 * (X:ℝ)^2 * Real.exp (2*(X:ℝ)) * Real.exp 3 :=
      mul_le_mul_of_nonneg_left hmaxle (by positivity)
    refine le_trans hb ?_
    rw [hC]
    exact mul_le_mul_of_nonneg_left hgoal (norm_nonneg _)
  calc ‖(bprod (7.2*(X:ℝ)) X x)^(Tp+1)‖
      = ‖bprod (7.2*(X:ℝ)) X x‖^(Tp+1) := by rw [norm_pow]
    _ ≤ (‖bprod (7.2*(X:ℝ)) X z‖ * (C * Real.exp 3))^(Tp+1) :=
        pow_le_pow_left₀ (by positivity) hstep _
    _ = ‖(bprod (7.2*(X:ℝ)) X z)^(Tp+1)‖ * Real.exp (((Tp:ℝ)+1) * (Real.log C + 3)) := by
        have hcast : (((Tp+1 : ℕ)) : ℝ) = (Tp:ℝ) + 1 := by push_cast; ring
        have h1 : C^(Tp+1) = Real.exp (((Tp:ℝ)+1) * Real.log C) := by
          conv_lhs => rw [show C = Real.exp (Real.log C) from (Real.exp_log hCpos).symm]
          rw [← hcast, ← Real.exp_nat_mul]
        have h2 : (Real.exp 3)^(Tp+1) = Real.exp (((Tp:ℝ)+1)*3) := by
          rw [← hcast, ← Real.exp_nat_mul]
        rw [mul_pow, mul_pow, norm_pow, h1, h2, ← Real.exp_add]
        congr 1
        ring

/-- BW §19 last step (p. 55–56) at level `J`: from `|s| ≤ 2^{r-1}S^{(J)}`, `|t| ≤ ξ^{r-1}T^{(J)}` to the half-integers `g^{(J)}(s/2;t) = 0`, `|s| ≤ 4S^{(J)}`, `|t| ≤ ξ^rT^{(J)}`. Even `s` are integers already covered; for odd `s`: `extrap_core` at `s/2` with `S' = ⌊2^{r-1}S^{(J)}⌋`, `R = 7·2S'`, `κ = ½`, `η = 1/3`; `U` from `est18`, `V` from `est22`; `W`: `(23)` gives `log|F(s/2)| ≤ −(2S'+1)(T'+1) log 7·2`; conditions from `num19_half`. -/
theorem extrap_half_step {K : Type*} [Field K] [NumberField K] {n r : ℕ} {φ : K →+* ℂ} {α : Fin n → K}
    {b : Fin n → ℤ} {k : Fin n} {c : ℝ} {v : ℕ} {L : Fin r → Fin n → ℤ} {α' : Fin r → K}
    {σ : Fin r → ℝ} {ι : Fin (r - 1) → Fin n}
    {p : AuxIdx r (acH K b v) (pD0 r (dK K) σ) (pDj r (dK K) σ) → K}
    (H : ACHyp φ α b k c v L α' σ ι p) (J : ℕ) (hJ : J ≤ pI r (dK K))
    (hnd : ∃ j, (2 : ℝ) ^ J ≤ (pDj r (dK K) σ j : ℝ)) (μ : Fin r → ℕ)
    (hvan : VanSet (fun i => lamP φ α v L i) (QJ φ b k L ι v σ p J μ) (ballZ (2 ^ (r - 1) * SJ K r b v J)) 1 (pxi r ^ (r - 1) * TJ K σ J)) :
    VanSet (fun i => lamP φ α v L i) (QJ φ b k L ι v σ p J μ) (ballZ (4 * SJ K r b v J)) 2 (pxi r ^ r * TJ K σ J) := by
  classical
  simp only [VanSet, ballZ, Set.mem_setOf_eq] at hvan ⊢
  intro s hs t0 t ht
  have hr2top : 2 ≤ r := H.hr
  rcases Int.even_or_odd s with hev | hod
  · -- even case
    obtain ⟨u, hu⟩ := hev
    subst hu
    have hs' : ((|u| : ℤ) : ℝ) ≤ 2 ^ (r - 1) * SJ K r b v J := by
      have h1 : ((|(u + u : ℤ)| : ℤ) : ℝ) = 2 * ((|u| : ℤ) : ℝ) := by
        rw [show u + u = 2 * u by ring, abs_mul]
        push_cast
        ring
      have hSp : (0:ℝ) ≤ SJ K r b v J := by
        rw [SJ]
        exact mul_nonneg (zpow_nonneg (pxi_nonneg_h r) _) (by positivity)
      have h2pow : (2:ℝ) ≤ 2 ^ (r - 1) := by
        have hle : (1:ℕ) ≤ r - 1 := by omega
        have := Nat.pow_le_pow_right (by norm_num : 1 ≤ 2) hle
        have h2 : (2:ℝ)^(1:ℕ) ≤ (2:ℝ)^(r-1) := by exact_mod_cast this
        simpa using h2
      nlinarith [hs, h1, hSp, h2pow]
    have ht' : ((t0 + ∑ m, t m : ℕ) : ℝ) ≤ pxi r ^ (r - 1) * TJ K σ J := by
      have hξpos : 0 < pxi r := pxi_pos_h hr2top
      have hξle : pxi r ≤ 1 := pxi_le_one_h r
      have hTJ : 0 ≤ TJ K σ J := by
        rw [TJ]; exact mul_nonneg (pow_nonneg hξpos.le _) (by positivity)
      have hp : pxi r ^ r ≤ pxi r ^ (r - 1) :=
        pow_le_pow_of_le_one hξpos.le hξle (by omega)
      nlinarith only [ht, hTJ, hp]
    have hthis := hvan u hs' t0 t ht'
    have hgoal : ((u + u : ℤ) : ℂ) / ((2:ℕ) : ℂ) = (u : ℂ) := by push_cast; ring
    simpa only [hgoal, Nat.cast_one, div_one] using hthis
  · -- odd case
    have hodd : Odd s := hod
    by_cases hg0 : acg φ α b k L ι v σ p J μ t0 t ((s : ℂ) / 2) = 0
    · exact hg0
    exfalso
    set ξ : ℝ := pxi r with hξ
    set Ξ : ℝ := ξ ^ r with hΞ
    set S₀ : ℝ := acS K r b v with hS₀
    set T₀ : ℝ := acT K σ with hT₀
    set Dm : ℝ := acD K σ with hDm
    set hh : ℝ := (acH K b v : ℝ) with hhh
    set dd : ℝ := (dK K : ℝ) with hdd
    set SJv : ℝ := SJ K r b v J with hSJv
    set TJv : ℝ := TJ K σ J with hTJv
    set Sp : ℝ := 2 ^ (r - 1) * SJv with hSp
    set X : ℕ := ⌊Sp⌋₊ with hX
    set R : ℝ := 7.2 * (X : ℝ) with hR
    set Tp : ℕ := ⌊(1 - ξ) * ξ ^ (r - 1) * TJv⌋₊ with hTp
    set ZZ : Finset ℤ := Finset.Icc (-(X : ℤ)) (X : ℤ) with hZZ
    set sc : ℂ := (s : ℂ) / 2 with hsc
    set δ : ℝ := R - ‖sc‖ with hδ
    set f : ℂ → ℂ := acf φ α b k L ι v σ p J μ t0 t with hf
    set U : ℝ := 2 ^ r * (dd * hh * (ξ ^ r * TJv) + 1.087 * S₀ * Dm +
        1.008 * ((R / 2 ^ r + ((|s| : ℤ) : ℝ) / 2) / 2 ^ J) * Dm + kumJ K b v σ J) with hUdef
    set V : ℝ := 2 ^ r * (dd * hh * (ξ ^ (r - 1) * TJv) - 7.893 * S₀ * Dm +
        1.01 * (((X : ℝ) / 2 ^ r + ((|s| : ℤ) : ℝ) / 2) / 2 ^ J) * Dm + kumJ K b v σ J) with hVdef
    set W : ℝ := (2 * (X : ℝ) + 1) * ((Tp : ℝ) + 1) * Real.log 7.2 - 3 * ((Tp : ℝ) + 1) with hWdef
    set Y : ℝ := ((Tp : ℝ) + 1) * (Real.log ((2 * Real.pi * (1/3 : ℝ))⁻¹ * (1 - 1/3)⁻¹ ^ 2 *
        (X : ℝ) ^ 2 * Real.exp (2 * (X : ℝ))) + 3) with hYdef
    have hgsc : acg φ α b k L ι v σ p J μ t0 t ((s : ℂ) / 2) ≠ 0 := hg0
    -- ============ basic facts ============
    have hr2 : 2 ≤ r := H.hr
    have hξpos : 0 < ξ := by rw [hξ]; exact pxi_pos_h hr2
    have hξle1 : ξ ≤ 1 := by rw [hξ]; exact pxi_le_one_h r
    have hΞpos : 0 < Ξ := by rw [hΞ]; positivity
    have hΞle1 : Ξ ≤ 1 := by rw [hΞ]; exact pow_le_one₀ (le_of_lt hξpos) hξle1
    have hd1 : 1 ≤ dK K := by
      show 1 ≤ Module.finrank ℚ K
      exact Module.finrank_pos
    have hσ : ∀ j, 1 / (dK K : ℝ) ≤ σ j := fun j => sigma_ge H j
    have hh19 : 19 ≤ acH K b v := (acH_lower H).1
    obtain ⟨hT1, hT2, hT3, hS608⟩ := num_T (d := dK K) (h := acH K b v) hr2 hd1 hh19 σ hσ
    have hT1' : 6.297 * Dm ≤ (1 - ξ) * T₀ := by
      simpa only [hDm, hT₀, hξ] using hT1
    have hT2' : (1 - ξ) * T₀ ≤ 6.3 * Dm := by
      simpa only [hDm, hT₀, hξ] using hT2
    have hT3' : dd * hh * T₀ ≤ 0.735 * S₀ * Dm := by
      simpa only [hDm, hT₀, hdd, hhh, hS₀] using hT3
    have hS608' : (608:ℝ) ≤ S₀ := by rw [hS₀]; exact hS608
    obtain ⟨hDlow, hDjr⟩ := num_D_lower (d := dK K) hr2 hd1 σ hσ
    have hDlow' : 2 * (r:ℝ)^r * 32^(r+1) * (dK K : ℝ) * Real.log (2 * r * (dK K : ℝ)) ≤ Dm := by
      rw [hDm]; exact hDlow
    have hDmpos : 0 < Dm := by
      have h1r : (1:ℝ) ≤ (r:ℝ) := by exact_mod_cast (le_trans (by norm_num) hr2)
      have h1d : (1:ℝ) ≤ (dK K : ℝ) := by exact_mod_cast hd1
      have hlogpos : (0:ℝ) < Real.log (2 * (r:ℝ) * (dK K : ℝ)) :=
        Real.log_pos (by nlinarith)
      have hpos : (0:ℝ) < 2 * (r:ℝ)^r * 32^(r+1) * (dK K : ℝ) *
          Real.log (2 * (r:ℝ) * (dK K : ℝ)) := by positivity
      linarith only [hDlow', hpos]
    have hacDpos : (0:ℝ) < acD K σ := by rw [← hDm]; exact hDmpos
    obtain ⟨hΞinv87, hΞ535, hξr1le, hξjge, h2Ξge⟩ := num_xi hr2
    have h2Ξge' : 1.07 ≤ 2 * Ξ := by rw [hΞ, hξ]; exact h2Ξge
    have hSJ_eq : SJv = (Ξ⁻¹)^J * S₀ := by
      rw [hSJv, hS₀, hΞ]
      exact SJ_eq K r b v J
    have hTJ_eq : TJv = Ξ^J * T₀ := by
      rw [hTJv, hT₀, hΞ]
      exact TJ_eq K σ J
    have hT0nn : (0:ℝ) ≤ T₀ := by rw [hT₀]; positivity
    have hS0nn : (0:ℝ) ≤ S₀ := by rw [hS₀]; positivity
    have hSJv608 : (608:ℝ) ≤ SJv := by
      have h1 : (1:ℝ) ≤ (Ξ⁻¹)^J := one_le_pow₀ (by rw [one_le_inv₀ hΞpos]; exact hΞle1)
      rw [hSJ_eq]
      nlinarith only [h1, hS608']
    have hXnn : (0:ℝ) ≤ Sp := by rw [hSp]; positivity
    have hXle : (X:ℝ) ≤ Sp := by show (⌊Sp⌋₊ : ℝ) ≤ Sp; exact Nat.floor_le hXnn
    have hXlt : Sp < (X:ℝ) + 1 := by show Sp < (⌊Sp⌋₊ : ℝ) + 1; exact Nat.lt_floor_add_one Sp
    have h2r : (2:ℝ) ≤ 2^(r-1) := by
      have hle : (1:ℕ) ≤ r - 1 := by omega
      have := Nat.pow_le_pow_right (by norm_num : 1 ≤ 2) hle
      have h2 : (2:ℝ)^(1:ℕ) ≤ (2:ℝ)^(r-1) := by exact_mod_cast this
      simpa using h2
    have hSp_ge : 2 * SJv ≤ Sp := by rw [hSp]; nlinarith only [h2r, hSJv608]
    have hX1 : 1 ≤ X := by
      have h : (1:ℝ) < (X:ℝ) + 1 := by
        have hSp1 : (1:ℝ) ≤ Sp := by nlinarith only [hSJv608, hSp_ge]
        linarith [hXlt]
      have h' : (1:ℕ) < X + 1 := by exact_mod_cast h
      omega
    have hSp_le' : Sp ≤ (X:ℝ) + 1 := le_of_lt hXlt
    have hTJnn : (0:ℝ) ≤ TJv := by rw [hTJ_eq]; positivity
    have hTp_le : (Tp:ℝ) ≤ (1 - ξ) * ξ ^ (r - 1) * TJv := by
      rw [hTp]
      refine Nat.floor_le ?_
      exact mul_nonneg (mul_nonneg (by linarith [hξle1]) (pow_nonneg hξpos.le _)) hTJnn
    have hTp_lt : (1 - ξ) * ξ ^ (r - 1) * TJv < (Tp:ℝ) + 1 := by
      rw [hTp]; exact Nat.lt_floor_add_one _
    have hTpnn : (0:ℝ) ≤ (Tp:ℝ) := by positivity
    have hZmem : ∀ l ∈ ZZ, ((|l| : ℤ) : ℝ) ≤ (X:ℝ) := by
      intro l hl
      rw [hZZ, Finset.mem_Icc] at hl
      have h1 : |l| ≤ (X:ℤ) := by
        rw [abs_le]; exact ⟨by linarith [hl.1], hl.2⟩
      exact_mod_cast h1
    have hZmem' : ∀ l ∈ ZZ, |l| ≤ (X:ℤ) := by
      intro l hl
      rw [hZZ, Finset.mem_Icc] at hl
      rw [abs_le]; exact ⟨by linarith [hl.1], hl.2⟩
    have hcard : (ZZ.card : ℝ) = 2 * (X:ℝ) + 1 := by
      rw [hZZ]
      have h1 : (Finset.Icc (-(X:ℤ)) (X:ℤ)).card = (2 * X + 1 : ℕ) := by
        rw [Int.card_Icc, show (X:ℤ) + 1 - (-(X:ℤ)) = 2 * (X:ℤ) + 1 by ring]
        have h2 : ((2 * (X:ℤ) + 1).toNat : ℤ) = 2 * (X:ℤ) + 1 :=
          Int.toNat_of_nonneg (by omega)
        omega
      rw [h1]
      push_cast
      ring
    have hsc_norm : ‖sc‖ = ((|s| : ℤ) : ℝ) / 2 := by
      rw [hsc, norm_div, Complex.norm_intCast, ← Int.cast_abs]
      norm_num
    have hsc_le : ‖sc‖ ≤ 2 * SJv := by
      rw [hsc_norm]
      have h1 : ((|s| : ℤ) : ℝ) ≤ 4 * SJv := hs
      linarith only [h1]
    have hs18 : ((|s| : ℤ) : ℝ) / 2 ^ J ≤ 4 * acS K r b v := by
      have h1 : ((|s| : ℤ) : ℝ) ≤ 4 * ((Ξ⁻¹)^J * S₀) := by
        have h1a : ((|s| : ℤ) : ℝ) ≤ 4 * SJv := hs
        linarith only [h1a, hSJ_eq]
      have h2 : (Ξ⁻¹ / 2 : ℝ) ^ J ≤ 1 := by
        apply pow_le_one₀ (by positivity)
        have heq : Ξ⁻¹ / 2 = (2*Ξ)⁻¹ := by rw [div_eq_mul_inv, mul_comm, ← mul_inv, mul_comm]
        rw [heq, inv_le_one₀ (by positivity)]
        linarith only [h2Ξge']
      have h5 : (Ξ⁻¹)^J ≤ 2^J := by
        have h6 : (Ξ⁻¹)^J / 2^J ≤ 1 := by rw [← div_pow]; exact h2
        rwa [div_le_one (by positivity)] at h6
      have h4 : ((Ξ⁻¹)^J * S₀) / 2^J ≤ S₀ := by
        rw [div_le_iff₀ (by positivity)]
        nlinarith only [h5, hS0nn]
      have h3 : 4 * ((Ξ⁻¹)^J * S₀) / 2^J ≤ 4 * acS K r b v := by
        rw [show 4 * ((Ξ⁻¹)^J * S₀) / 2^J = 4 * (((Ξ⁻¹)^J * S₀) / 2^J) by ring]
        rw [hS₀]
        linarith only [h4]
      have h7 : ((|s| : ℤ) : ℝ) / 2^J ≤ 4 * ((Ξ⁻¹)^J * S₀) / 2^J :=
        div_le_div_of_nonneg_right h1 (by positivity)
      linarith only [h7, h3]
    have ht1 : ((t0 + ∑ m, t m : ℕ) : ℝ) ≤ ξ ^ r * TJv := by
      simpa only [hξ, hTJv] using ht
    have ht2 : ((t0 + ∑ m, t m : ℕ) : ℝ) ≤ ξ ^ (r - 1) * TJv := by
      have hp : ξ ^ r ≤ ξ ^ (r - 1) := pow_le_pow_of_le_one hξpos.le hξle1 (by omega)
      nlinarith only [ht1, hp, hTJnn]
    have hTst1' : ξ ^ r * TJv ≤ acT K σ := by
      rw [← hT₀, hTJ_eq]
      have hp : Ξ ^ (J+1) ≤ 1 := pow_le_one₀ hΞpos.le hΞle1
      calc ξ ^ r * (Ξ ^ J * T₀) = Ξ ^ (J+1) * T₀ := by rw [← hΞ, pow_succ']; ring
        _ ≤ T₀ := by nlinarith only [hp, hT0nn]
    -- ============ U from est18 ============
    have hU : ∀ z : ℂ, ‖z‖ = R → ‖f z‖ ≤ ‖f sc‖ * Real.exp U := by
      intro z hz
      have h18 := est18 H J hJ μ (ξ ^ r * TJv) hTst1' t0 t ht1 s hs18
        (by rw [← hsc]; exact hgsc) z
      simpa only [hf, hsc, hUdef, hdd, hhh, hS₀, hDm, hz] using h18
    -- ============ V from est22 ============
    have hV : ∀ l ∈ ZZ, ∀ m ≤ Tp, ‖taylorC f m (l:ℂ)‖ ≤ ‖f sc‖ * Real.exp V := by
      intro l hl m hm
      have hlX : ((|l| : ℤ) : ℝ) ≤ (X:ℝ) := hZmem l hl
      have hnl : ‖((l:ℂ))‖ ≤ (X:ℝ) := by
        rw [Complex.norm_intCast, ← Int.cast_abs]; exact hlX
      have hsumT : (Tp:ℝ) + ξ ^ r * TJv ≤ ξ ^ (r-1) * TJv := by
        have hp : ξ ^ r = ξ ^ (r-1) * ξ := by
          conv_lhs => rw [show r = (r-1) + 1 by omega]
          rw [pow_succ', mul_comm]
        have hp2 : ξ * ξ ^ (r-1) = ξ ^ r := by rw [mul_comm, ← hp]
        have hkey : (1 - ξ) * ξ ^ (r-1) * TJv = ξ ^ (r-1) * TJv - ξ ^ r * TJv := by
          rw [← hp2]; ring
        linarith only [hTp_le, hkey]
      have hTst2 : ξ ^ (r - 1) * TJv ≤ acT K σ := by
        rw [← hT₀, hTJ_eq]
        have hp : Ξ ^ J ≤ 1 := pow_le_one₀ hΞpos.le hΞle1
        have hξr1 : ξ ^ (r-1) ≤ 1 := pow_le_one₀ hξpos.le hξle1
        have hT0' : Ξ ^ J * T₀ ≤ T₀ := by nlinarith only [hp, hT0nn]
        have h1 := mul_le_mul hξr1 hT0' (mul_nonneg (pow_nonneg hΞpos.le J) hT0nn)
          (by norm_num : (0:ℝ) ≤ 1)
        linarith only [h1]
      have hv22 : ∀ (t0' : ℕ) (t' : Fin (r - 1) → ℕ),
          ((t0' + ∑ mm, t' mm : ℕ) : ℝ) ≤ (Tp:ℝ) + ξ ^ r * TJv →
          acg φ α b k L ι v σ p J μ t0' t' ((l:ℂ)) = 0 := by
        intro t0' t' hlt
        have h2 : ((|l| : ℤ) : ℝ) ≤ 2 ^ (r - 1) * SJ K r b v J := by
          have h2a : 2 ^ (r-1) * SJ K r b v J = Sp := by rw [← hSp]
          rw [h2a]
          linarith only [hlX, hXle]
        have h3 : ((t0' + ∑ mm, t' mm : ℕ) : ℝ) ≤ pxi r ^ (r - 1) * TJ K σ J := by
          have h3a : pxi r ^ (r-1) * TJ K σ J = ξ ^ (r-1) * TJv := by rw [hξ, hTJv]
          rw [h3a]
          linarith only [hlt, hsumT]
        have hres := hvan l h2 t0' t' h3
        simpa only [Nat.cast_one, div_one] using hres
      have h22 := est22 H J hJ μ (ξ^(r-1)*TJv) hTst2 (Tp:ℝ) (ξ^r*TJv) hTpnn hsumT
        ((l:ℂ)) hv22 t0 t ht1 m (by exact_mod_cast hm) s hs18 (by rw [← hsc]; exact hgsc)
      have h22' : ‖taylorC f m (l:ℂ)‖ ≤ ‖f sc‖ * Real.exp (2^r *
          ((dK K : ℝ) * (acH K b v : ℝ) * (ξ^(r-1)*TJv) - 7.893 * acS K r b v * acD K σ +
            1.01 * ((‖((l:ℂ))‖ / 2^r + ((|s| : ℤ) : ℝ) / 2) / 2^J) * acD K σ + kumJ K b v σ J)) := by
        simpa only [hf, hsc] using h22
      refine le_trans h22' ?_
      apply mul_le_mul_of_nonneg_left _ (norm_nonneg _)
      apply Real.exp_le_exp.mpr
      have hml : (‖((l:ℂ))‖ / 2^r + ((|s| : ℤ) : ℝ) / 2) / 2^J ≤
          ((X:ℝ) / 2^r + ((|s| : ℤ) : ℝ) / 2) / 2^J := by
        apply div_le_div_of_nonneg_right _ (pow_pos (by norm_num : (0:ℝ) < 2) J).le
        exact add_le_add (div_le_div_of_nonneg_right hnl
          (pow_pos (by norm_num : (0:ℝ) < 2) r).le) le_rfl
      have hExp : 2^r * ((dK K : ℝ) * (acH K b v : ℝ) * (ξ^(r-1)*TJv) -
            7.893 * acS K r b v * acD K σ +
            1.01 * ((‖((l:ℂ))‖ / 2^r + ((|s| : ℤ) : ℝ) / 2) / 2^J) * acD K σ + kumJ K b v σ J)
          ≤ 2^r * ((dK K : ℝ) * (acH K b v : ℝ) * (ξ^(r-1)*TJv) -
            7.893 * acS K r b v * acD K σ +
            1.01 * (((X:ℝ) / 2^r + ((|s| : ℤ) : ℝ) / 2) / 2^J) * acD K σ + kumJ K b v σ J) := by
        apply mul_le_mul_of_nonneg_left _ (by positivity : (0:ℝ) ≤ 2^r)
        have h3 := mul_le_mul_of_nonneg_right hml (by positivity : (0:ℝ) ≤ acD K σ)
        nlinarith only [h3]
      rw [hVdef, hdd, hhh, hS₀, hDm]
      exact hExp
    -- ============ W from (23) ============
    have hWnum : ‖∏ l ∈ ZZ, bfac R l sc ^ (Tp + 1)‖ ≤ Real.exp (-W) := by
      have h1 : ∏ l ∈ ZZ, bfac R l sc ^ (Tp + 1) = (bprod R X sc) ^ (Tp + 1) := by
        rw [hZZ, hR, bprod, Finset.prod_pow]
      have hscR : sc = ((((s:ℤ):ℝ)/2 : ℝ) : ℂ) := by rw [hsc]; push_cast; ring
      have hx' : |(((s:ℤ):ℝ)/2)| ≤ (X:ℝ) + 1 := by
        have h1' : ((|s| : ℤ) : ℝ) ≤ 4 * SJv := hs
        rw [abs_div, abs_of_pos (by norm_num : (0:ℝ) < 2), ← Int.cast_abs]
        linarith only [h1', hSp_ge, hSp_le']
      have hbpos := bprod_pow_le_exp' X Tp (((s:ℤ):ℝ)/2) hX1 hx'
      have hgoal : ‖(bprod R X sc) ^ (Tp + 1)‖ ≤ Real.exp (-W) := by
        rw [hR, hscR]
        have hWneg : -W = -((2 * (X:ℝ) + 1) * ((Tp:ℝ) + 1) * Real.log 7.2) + 3 * ((Tp:ℝ) + 1) := by
          rw [hWdef]; ring
        rw [hWneg]
        exact hbpos
      rwa [h1]
    -- ============ Y from (24) ============
    have hYnum : ∀ l ∈ ZZ, ∀ z : ℂ, ‖z - (l:ℂ)‖ = (1/3:ℝ) →
        ‖∏ l' ∈ ZZ, bfac R l' sc ^ (Tp + 1)‖ ≤
          ‖∏ l' ∈ ZZ, bfac R l' z ^ (Tp + 1)‖ * Real.exp Y := by
      intro l hl z hz
      have hlX : |l| ≤ (X:ℤ) := hZmem' l hl
      have hscR : sc = ((((s:ℤ):ℝ)/2 : ℝ) : ℂ) := by rw [hsc]; push_cast; ring
      have hx' : |(((s:ℤ):ℝ)/2)| ≤ (X:ℝ) + 1 := by
        have h1' : ((|s| : ℤ) : ℝ) ≤ 4 * SJv := hs
        rw [abs_div, abs_of_pos (by norm_num : (0:ℝ) < 2), ← Int.cast_abs]
        linarith only [h1', hSp_ge, hSp_le']
      have hb := bprod_ratio_pow_le' X Tp (((s:ℤ):ℝ)/2) z l (1/3) hX1 (by norm_num) (by norm_num)
        hx' hlX hz
      have h1a : ∏ l' ∈ ZZ, bfac R l' sc ^ (Tp + 1) = (bprod R X sc) ^ (Tp + 1) := by
        rw [hZZ, hR, bprod, Finset.prod_pow]
      have h1b : ∏ l' ∈ ZZ, bfac R l' z ^ (Tp + 1) = (bprod R X z) ^ (Tp + 1) := by
        rw [hZZ, hR, bprod, Finset.prod_pow]
      have hgoal : ‖(bprod R X sc) ^ (Tp + 1)‖ ≤
          ‖(bprod R X z) ^ (Tp + 1)‖ * Real.exp Y := by
        rw [hR, hscR, hYdef]
        exact hb
      rwa [h1a, h1b]
    -- ============ f sc ≠ 0 from est_f_ge_half_g ============
    have hfg : ‖acg φ α b k L ι v σ p J μ t0 t sc‖ ≤ 2 * ‖acf φ α b k L ι v σ p J μ t0 t sc‖ := by
      have h := (est_f_ge_half_g H J hJ μ (ξ ^ r * TJv) hTst1' t0 t ht1 s).2 hs18
      rwa [← hsc] at h
    have hfsc : f sc ≠ 0 := by
      intro hzero
      have h1 : ‖acf φ α b k L ι v σ p J μ t0 t sc‖ = 0 := by rw [← hf, hzero, norm_zero]
      have h2 : ‖acg φ α b k L ι v σ p J μ t0 t sc‖ = 0 := by
        have h3 := hfg
        rw [h1, mul_zero] at h3
        exact le_antisymm h3 (norm_nonneg _)
      exact hgsc (norm_eq_zero.mp h2)
    have hh19' : (19:ℝ) ≤ hh := by rw [hhh]; exact_mod_cast hh19
    have hJ50 : (J:ℝ) ≤ 50 * Real.log (2*(r:ℝ)*(dK K:ℝ)) := by
      have h := hJ
      have h' : (J:ℝ) ≤ ((pI r (dK K) : ℕ) : ℝ) := by exact_mod_cast h
      have h'' : ((pI r (dK K) : ℕ) : ℝ) ≤ 50 * Real.log (2*(r:ℝ)*(dK K:ℝ)) := by
        have hlogpos : (0:ℝ) < Real.log (2*(r:ℝ)*(dK K:ℝ)) := by
          have h1r : (1:ℝ) ≤ (r:ℝ) := by exact_mod_cast (le_trans (by norm_num) hr2)
          have h1d : (1:ℝ) ≤ (dK K:ℝ) := by exact_mod_cast hd1
          exact Real.log_pos (by nlinarith only [h1r, h1d])
        have hfl := Nat.floor_le (show (0:ℝ) ≤ 50 * Real.log (2 * (r:ℝ) * (dK K:ℝ)) by positivity)
        simpa only [pI] using hfl
      linarith only [h', h'']
    -- ============ the two numerical conditions ============
    have hDmpos' := hDmpos
    have hX1'' : (1:ℝ) ≤ (X:ℝ) := by exact_mod_cast hX1
    have hδpos : 0 < δ := by
      have h1 : ‖sc‖ ≤ R/2 := by
        rw [hR]
        have h2 : (X:ℝ) + 1 ≤ 7.2 * (X:ℝ) / 2 := by nlinarith only [hX1'']
        linarith only [hsc_le, hSp_ge, hSp_le', h2]
      rw [hδ]; linarith
    have hδge : R/2 ≤ δ := by
      rw [hδ, hR]
      have h2 : (X:ℝ) + 1 ≤ 7.2 * (X:ℝ) / 2 := by nlinarith only [hX1'']
      linarith only [hsc_le, hSp_ge, hSp_le', h2]
    have hsc_norm' : ((|s| : ℤ) : ℝ) / 2 ≤ 2 * (Ξ⁻¹)^J * S₀ := by
      have h := hsc_le
      rw [hsc_norm, hSJ_eq] at h
      simpa only [mul_assoc] using h
    -- the exact vocabulary of the numeric lemmas
    have hXleΞ : (X:ℝ) ≤ 2^(r-1) * (Ξ⁻¹)^J * S₀ := by
      have h := hXle
      rw [hSp] at h
      rw [hSJ_eq] at h
      simpa only [mul_assoc] using h
    have hXltΞ : 2^(r-1) * (Ξ⁻¹)^J * S₀ < (X:ℝ) + 1 := by
      have h := hXlt
      rw [hSp] at h
      rw [hSJ_eq] at h
      simpa only [mul_assoc] using h
    have hTpleΞ : (Tp:ℝ) ≤ (1-ξ) * ξ^(r-1) * (Ξ^J * T₀) := by
      have h := hTp_le
      rw [hTJ_eq] at h
      exact h
    have hTpltΞ : (1-ξ) * ξ^(r-1) * (Ξ^J * T₀) < (Tp:ℝ) + 1 := by
      have h := hTp_lt
      rw [hTJ_eq] at h
      exact h
    have hδgeΞ : 3.6 * (X:ℝ) ≤ δ := by
      have h := hδge
      rw [hR] at h
      linarith only [h]
    have hξS : (1 - ξ) * S₀ = 8.576 * (dK K : ℝ) * hh := by
      have hr0 : (r:ℝ) ≠ 0 := by positivity
      have h1 : (1 - ξ) = 0.536 / (r:ℝ) := by
        rw [hξ]; simp only [pxi]; ring
      have h2 : S₀ = 16 * (r:ℝ) * (dK K : ℝ) * (acH K b v : ℝ) := by
        rw [hS₀]; simp only [acS, pS]; push_cast; ring
      rw [h1, h2, hhh]
      field_simp
      ring
    -- U bound
    have hUbound : U ≤ 2^r * ((dK K : ℝ) * hh * (Ξ^(J+1) * T₀) + 1.087 * S₀ * Dm +
        1.008 * ((7.2 * (X:ℝ) / 2^r + 2 * (Ξ⁻¹)^J * S₀) / 2^J) * Dm +
        0.044 * J / Real.log (2*(r:ℝ)*(dK K : ℝ)) * S₀ * Dm) := by
      have key : (dK K : ℝ) * hh * (ξ^r * TJv) = (dK K : ℝ) * hh * (Ξ^(J+1) * T₀) := by
        rw [hTJ_eq, ← hΞ, pow_succ']; ring
      have hkum : kumJ K b v σ J =
          0.044 * J / Real.log (2*(r:ℝ)*(dK K : ℝ)) * S₀ * Dm := by
        rw [kumJ, hS₀, hDm]
      have hthird : 1.008 * ((R / 2 ^ r + ((|s| : ℤ) : ℝ) / 2) / 2 ^ J) * Dm ≤
          1.008 * ((7.2 * (X:ℝ) / 2^r + 2 * (Ξ⁻¹)^J * S₀) / 2^J) * Dm := by
        have h1 : R / 2^r + ((|s| : ℤ) : ℝ) / 2 ≤ 7.2 * (X:ℝ) / 2^r + 2 * (Ξ⁻¹)^J * S₀ := by
          rw [hR]; linarith only [hsc_norm']
        have h2 : (0:ℝ) < 2^J := by positivity
        have h3 : (R / 2^r + ((|s| : ℤ) : ℝ) / 2) / 2^J ≤
            (7.2 * (X:ℝ) / 2^r + 2 * (Ξ⁻¹)^J * S₀) / 2^J :=
          div_le_div_of_nonneg_right h1 h2.le
        have h4 : (0:ℝ) ≤ Dm := le_of_lt hDmpos
        exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left h3 (by norm_num)) h4
      rw [hUdef, hdd, hkum, key]
      have hbr : (dK K : ℝ) * hh * (Ξ^(J+1) * T₀) + 1.087 * S₀ * Dm +
            1.008 * ((R / 2^r + ((|s| : ℤ) : ℝ) / 2) / 2^J) * Dm +
            0.044 * J / Real.log (2*(r:ℝ)*(dK K : ℝ)) * S₀ * Dm
          ≤ (dK K : ℝ) * hh * (Ξ^(J+1) * T₀) + 1.087 * S₀ * Dm +
            1.008 * ((7.2 * (X:ℝ) / 2^r + 2 * (Ξ⁻¹)^J * S₀) / 2^J) * Dm +
            0.044 * J / Real.log (2*(r:ℝ)*(dK K : ℝ)) * S₀ * Dm := by
        linarith only [hthird]
      exact mul_le_mul_of_nonneg_left hbr (by positivity : (0:ℝ) ≤ 2^r)
    -- V bound
    have hVbound : V ≤ 2^r * ((dK K : ℝ) * hh * (ξ^(r-1) * (Ξ^J * T₀)) - 7.893 * S₀ * Dm +
        1.01 * (2.5 * (Ξ⁻¹)^J * S₀ / 2^J) * Dm +
        0.044 * J / Real.log (2*(r:ℝ)*(dK K : ℝ)) * S₀ * Dm) := by
      have key : (dK K : ℝ) * hh * (ξ^(r-1) * TJv) = (dK K : ℝ) * hh * (ξ^(r-1) * (Ξ^J * T₀)) := by
        rw [hTJ_eq]
      have hkum : kumJ K b v σ J =
          0.044 * J / Real.log (2*(r:ℝ)*(dK K : ℝ)) * S₀ * Dm := by
        rw [kumJ, hS₀, hDm]
      have hthird : 1.01 * (((X : ℝ) / 2 ^ r + ((|s| : ℤ) : ℝ) / 2) / 2 ^ J) * Dm ≤
          1.01 * (2.5 * (Ξ⁻¹)^J * S₀ / 2^J) * Dm := by
        have h1 : (X:ℝ) / 2^r + ((|s| : ℤ) : ℝ) / 2 ≤ 2.5 * (Ξ⁻¹)^J * S₀ := by
          have h2 : (X:ℝ) / 2^r ≤ (Ξ⁻¹)^J * S₀ / 2 := by
            rw [div_le_div_iff₀ (by positivity : (0:ℝ) < 2^r) (by norm_num : (0:ℝ) < 2)]
            have h2r' : (2:ℝ)^r = 2^(r-1) * 2 := by
              conv_lhs => rw [show r = (r-1) + 1 by omega]
              rw [pow_succ', mul_comm]
            nlinarith [hXleΞ, h2r']
          linarith only [h2, hsc_norm']
        have h2 : (0:ℝ) < 2^J := by positivity
        have h3 : ((X:ℝ) / 2^r + ((|s| : ℤ) : ℝ) / 2) / 2^J ≤ 2.5 * (Ξ⁻¹)^J * S₀ / 2^J :=
          div_le_div_of_nonneg_right h1 h2.le
        have h4 : (0:ℝ) ≤ Dm := le_of_lt hDmpos
        exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left h3 (by norm_num)) h4
      rw [hVdef, hdd, hkum, key]
      have hbr : (dK K : ℝ) * hh * (ξ^(r-1) * (Ξ^J * T₀)) - 7.893 * S₀ * Dm +
            1.01 * (((X:ℝ) / 2^r + ((|s| : ℤ) : ℝ) / 2) / 2^J) * Dm +
            0.044 * J / Real.log (2*(r:ℝ)*(dK K : ℝ)) * S₀ * Dm
          ≤ (dK K : ℝ) * hh * (ξ^(r-1) * (Ξ^J * T₀)) - 7.893 * S₀ * Dm +
            1.01 * (2.5 * (Ξ⁻¹)^J * S₀ / 2^J) * Dm +
            0.044 * J / Real.log (2*(r:ℝ)*(dK K : ℝ)) * S₀ * Dm := by
        linarith only [hthird]
      exact mul_le_mul_of_nonneg_left hbr (by positivity : (0:ℝ) ≤ 2^r)
    -- Y bound
    have hYbound : Y ≤ ((Tp:ℝ) + 1) * (2 * (2^(r-1) * (Ξ⁻¹)^J * S₀) +
        2 * Real.log (2^(r-1) * (Ξ⁻¹)^J * S₀) +
        Real.log ((2*Real.pi*(1/3:ℝ))⁻¹ * (1-1/3)⁻¹^2) + 3) := by
      rw [hYdef]
      have hSp_pos : 0 < 2^(r-1) * (Ξ⁻¹)^J * S₀ := by
        have h1 : (1:ℝ) ≤ 2^(r-1) := by nlinarith only [h2r]
        have h2 : (0:ℝ) < (Ξ⁻¹)^J := by positivity
        nlinarith [h1, h2, hS608']
      have hlog : Real.log (X:ℝ) ≤ Real.log (2^(r-1) * (Ξ⁻¹)^J * S₀) := by
        apply Real.log_le_log (by positivity)
        exact hXleΞ
      have hlogX : Real.log ((X:ℝ)^2) = 2 * Real.log (X:ℝ) := by
        rw [Real.log_pow]; push_cast; ring
      have hXb : 2 * (X:ℝ) ≤ 2 * (2^(r-1) * (Ξ⁻¹)^J * S₀) := by linarith only [hXleΞ]
      have hmul : Real.log ((2*Real.pi*(1/3:ℝ))⁻¹ * (1-1/3)⁻¹^2 * (X:ℝ)^2 * Real.exp (2*(X:ℝ))) =
          Real.log ((2*Real.pi*(1/3:ℝ))⁻¹ * (1-1/3)⁻¹^2) + Real.log ((X:ℝ)^2) +
          Real.log (Real.exp (2*(X:ℝ))) := by
        rw [Real.log_mul (by positivity) (by positivity),
            Real.log_mul (by positivity) (by positivity),
            Real.log_mul (by positivity) (by positivity)]
      rw [hmul, hlogX, Real.log_exp]
      have hTpnn : (0:ℝ) ≤ (Tp:ℝ) + 1 := by positivity
      have hkey : Real.log ((2*Real.pi*(1/3:ℝ))⁻¹ * (1-1/3)⁻¹^2) + 2 * Real.log (X:ℝ) +
          2 * (X:ℝ) + 3 ≤
          2 * (2^(r-1) * (Ξ⁻¹)^J * S₀) + 2 * Real.log (2^(r-1) * (Ξ⁻¹)^J * S₀) +
          Real.log ((2*Real.pi*(1/3:ℝ))⁻¹ * (1-1/3)⁻¹^2) + 3 := by
        linarith only [hlog, hXb]
      have hgoal : ((Tp:ℝ) + 1) * (Real.log ((2*Real.pi*(1/3:ℝ))⁻¹ * (1-1/3)⁻¹^2) +
          2 * Real.log (X:ℝ) + 2 * (X:ℝ) + 3) ≤
          ((Tp:ℝ) + 1) * (2 * (2^(r-1) * (Ξ⁻¹)^J * S₀) +
          2 * Real.log (2^(r-1) * (Ξ⁻¹)^J * S₀) +
          Real.log ((2*Real.pi*(1/3:ℝ))⁻¹ * (1-1/3)⁻¹^2) + 3) :=
        mul_le_mul_of_nonneg_left hkey hTpnn
      push_cast
      exact hgoal
    -- apply the numeric lemmas
    have h1num : Real.log (R / δ) + U - W < -Real.log 2 := by
      have h := half_num_J (ξ := ξ) (Ξ := Ξ) (S₀ := S₀) (Dm := Dm) (T₀ := T₀) (hh := hh)
        (δ := δ) (X := X) (Tp := Tp)
        hr2 hd1 J hJ50 hξ hΞ hS608' hDmpos hT0nn hh19'
        hDlow' hT1' hT2' hT3' hξS hXleΞ hXltΞ hTpleΞ hTpltΞ hδgeΞ hδpos
      have hW' : W = (2 * (X:ℝ) + 1) * ((Tp:ℝ) + 1) * Real.log 7.2 - 3 * ((Tp:ℝ) + 1) := hWdef
      rw [hR]
      linarith only [h, hUbound, hW']
    have h2num : Real.log ((ZZ.card : ℝ) * ((Tp:ℝ) + 1)) +
        Real.log ((1/3:ℝ) / ((1/2:ℝ) - 1/3)) + V + Y < -Real.log 2 := by
      have hlog2 : Real.log ((1/3:ℝ) / ((1/2:ℝ) - 1/3)) = Real.log 2 := by norm_num
      have hq0 : (0:ℝ) ≤ (Ξ⁻¹)^J / Dm :=
        div_nonneg (le_of_lt (pow_pos (inv_pos.mpr hΞpos) J)) (le_of_lt hDmpos)
      have hq1 : (Ξ⁻¹)^J / Dm ≤ (2*Ξ)⁻¹^J / (r:ℝ) := by
        obtain ⟨j, hj⟩ := hnd
        have hjr : ((pDj r (dK K) σ j : ℕ) : ℝ) ≤ Dm / (r:ℝ) := by
          have := hDjr j; rw [hDm]; exact this
        have hrpos : (0:ℝ) < (r:ℝ) := by positivity
        have h2Jpos : (0:ℝ) < 2^J := by positivity
        have hr2J : (r:ℝ) * 2^J ≤ Dm := by
          have h1 : (r:ℝ) * 2^J ≤ (r:ℝ) * (Dm / (r:ℝ)) :=
            mul_le_mul_of_nonneg_left (le_trans hj hjr) hrpos.le
          rwa [mul_div_cancel₀ _ hrpos.ne'] at h1
        have hΞinv : (0:ℝ) < (Ξ⁻¹)^J := pow_pos (inv_pos.mpr hΞpos) J
        have h2Ξinv : (2*Ξ)⁻¹^J = (2:ℝ)⁻¹^J * (Ξ⁻¹)^J := by rw [mul_inv, mul_pow, mul_comm]
        have h1 : (2:ℝ)^J * (2:ℝ)⁻¹^J = 1 := by
          rw [← mul_pow, mul_inv_cancel₀ (by norm_num : (2:ℝ) ≠ 0), one_pow]
        have hkey : (r:ℝ) ≤ (2:ℝ)⁻¹^J * Dm := by
          have hm := mul_le_mul_of_nonneg_right hr2J (by positivity : (0:ℝ) ≤ (2:ℝ)⁻¹^J)
          have h2 : ((r:ℝ) * 2^J) * (2:ℝ)⁻¹^J = (r:ℝ) := by rw [mul_assoc, h1, mul_one]
          rw [h2, mul_comm] at hm
          exact hm
        rw [h2Ξinv, div_le_div_iff₀ hDmpos hrpos]
        nlinarith only [hkey, hΞinv]
      have hq2 : (Ξ⁻¹)^J / Dm ≤ (Ξ⁻¹)^J /
          (2 * (r:ℝ)^r * 32^(r+1) * (dK K:ℝ) * Real.log (2*(r:ℝ)*(dK K:ℝ))) := by
        have hlowpos : (0:ℝ) < 2 * (r:ℝ)^r * 32^(r+1) * (dK K:ℝ) * Real.log (2*(r:ℝ)*(dK K:ℝ)) := by
          have hlogpos : (0:ℝ) < Real.log (2*(r:ℝ)*(dK K:ℝ)) := by
            have h1r : (1:ℝ) ≤ (r:ℝ) := by exact_mod_cast (le_trans (by norm_num) hr2)
            have h1d : (1:ℝ) ≤ (dK K:ℝ) := by exact_mod_cast hd1
            exact Real.log_pos (by nlinarith only [h1r, h1d])
          positivity
        rw [div_le_div_iff₀ hDmpos hlowpos]
        have hΞinvnn : (0:ℝ) ≤ (Ξ⁻¹)^J := le_of_lt (pow_pos (inv_pos.mpr hΞpos) J)
        nlinarith [hDlow', hΞinvnn]
      have h := half_num_I (ξ := ξ) (Ξ := Ξ) (S₀ := S₀) (Dm := Dm) (T₀ := T₀) (hh := hh)
        (X := X) (Tp := Tp) (q := (Ξ⁻¹)^J / Dm)
        hr2 hd1 J hJ50 hξ hΞ hS608' hDmpos hT0nn hh19'
        hDlow' hT1' hT2' hT3' rfl hq0 hq1 hq2 hXleΞ hXltΞ hTpleΞ hTpltΞ
      rw [hcard, hlog2]
      linarith only [h, hVbound, hYbound]
    -- ============ the hypotheses of extrap_core ============
    have hZcond : ∀ l ∈ ZZ, ((|l| : ℤ) : ℝ) + 1/3 < R := by
      intro l hl
      have h1 := hZmem l hl
      have hX1' : (1:ℝ) ≤ (X:ℝ) := by exact_mod_cast hX1
      rw [hR]; nlinarith only [h1, hX1'']
    have hsR : ‖sc‖ + δ ≤ R := by rw [hδ]; linarith
    have hsZcond : ∀ l ∈ ZZ, (1/2:ℝ) ≤ ‖sc - (l:ℂ)‖ := by
      intro l hl
      have hne : s - 2*l ≠ 0 := by
        intro hcon
        have he : s = l + l := by omega
        obtain ⟨mm, hm⟩ := hodd
        omega
      have hge : (1:ℝ) ≤ ((|s - 2*l| : ℤ) : ℝ) := by
        have h1 : (1:ℤ) ≤ |s - 2*l| := Int.one_le_abs hne
        exact_mod_cast h1
      rw [hsc, show (s:ℂ)/2 - (l:ℂ) = (((s - 2*l : ℤ)):ℂ)/2 by push_cast; ring]
      rw [norm_div, Complex.norm_intCast, ← Int.cast_abs]
      rw [show ‖(2:ℂ)‖ = 2 by norm_num]
      linarith only [hge]
    have hdis : Differentiable ℂ f := by
      rw [hf]
      exact differentiable_fAt (ellM φ α b k v L) (QJ φ b k L ι v σ p J μ t0 t)
    exact hfsc (extrap_core f hdis R (1/3) (1/2) δ (by norm_num) (by norm_num) ZZ hZcond Tp sc
      hδpos hsR (by norm_num) hsZcond U V W Y hU hV hWnum hYnum h1num h2num)
