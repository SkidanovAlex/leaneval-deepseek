import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Algebra.Order.Star.Real
import Submission.Work.BoseC3QAll.Est1.estT2sum_opZ
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Submission.Work.BoseC3QAll.Est1.estT2sum_opZ` — the normal-ordered half of FS `T₂`

This is the `T₂,op` (`eq:T2opprime`) half of piece **B** of FS
`eq:EstimateQ3Tilde1`, in the physical normalisation `Z²·Σ_k c_k⁻¹`:

  `Z²Σ_{k∈P_H} c_k⁻¹ T2OpF k Φ ≤ C·e1A·‖Φ‖² + (b/400)⟨gapOpT⟩ + (𝓁²/8)⟨R_{P_H^q}⟩`,
  `Z = z/ℓ³`, `c_k = (1-𝓁²)𝒟_k`.

## The route (FS `eq:T2prime`→`eq:T2opprime`)

Write `A_{sk} = ã_s + β_{sk}ã_{-s}†`, `b_q = a_q + α_qa_{-q}†`, and

  `T2OpF k Φ = Σ_{s,s'} γ_{sk}γ_{s'k}·⟨b_{s'-k}(A_{sk}Φ), b_{s-k}(A_{s'k}Φ)⟩`,
  `γ_{sk} = gA E s k = f_L(s)Ŵ₁(k)q3Denom(s,k)`.

1. **Cauchy–Schwarz / AM–GM** in the Fock form (`bp_le_half`) collapses the bilinear
   form into `Σ_{s,s'}γ_{sk}γ_{s'k}‖b_{s'-k}(A_{sk}Φ)‖²` (the index swap of the
   symmetric double sum; `OpZ_perK`).
2. **Commuting `b_{s'-k}` past `A_{sk}`** (`bOp_comp_Atil`): the commutator is the
   *scalar* `κ` of FS `eq:StoerrelseC` (`|κ| ≤ 128K₀²𝓁η`, `OpZ_kappa`), so the
   `s`-sum is absorbed by the `θ`-mode window (`OpZ_Atil_sum`) while the scalar
   residual is `O(K₀²𝓁η)`.
3. **The `k`-sum** with the weight `Z²c_k⁻¹Ŵ₁(k)²`: since `k ↦ s-k` is injective and
   lands in `P_H^q` (`PH_subset_PHq_sub`) and `𝒟_q ≥ ‖q‖²/4` there, the pointwise
   bound `c_k⁻¹Ŵ₁(k)² ≤ 2048K₀²K_H⁴a⁶𝒟_{s-k}` (`OpZ_cD_bd`) turns the `k`-sum into
   the reserve `Σ_{q∈P_H^q}𝒟_q b_q†b_q` (`OpZ_reserve`); the lattice weight
   `Σ_k Z²c_k⁻¹Ŵ₁(k)² ≤ 8ρ_zK₀a` is `sum_cD_W1sq_le`.
4. **The arithmetic**: the reserve coefficient is `≤ 𝓁²/8` (`OpZ_RE1`) and the scalar
   remainder is `≤ C·e1A` (`OpZ_Bterm`).  The gap term of the target is nonnegative
   (`gapOpT_qw_nonneg`) and is simply discarded.

All constants are the corpus's coarse ones; `C` and `t₀` depend only on `K₀`, `b₀`.
-/

noncomputable section
open scoped BigOperators
set_option maxHeartbeats 1000000
namespace Work.BoseC3QAll
namespace Est1
open Work.BoseB7
theorem estT2sum_opZ (K₀ b₀ : ℝ) (hb₀ : 0 < b₀) :
    ∃ C t₀ : ℝ, 0 ≤ C ∧ 0 < t₀ ∧
      ∀ {Mode : Type*} [AddCommGroup Mode] [Fintype Mode] [DecidableEq Mode]
        (F : Work.BoseB7.FockData Mode) (T : Work.BoseC3QAll.TildeData F) (E : Work.BoseB7.Q3Env Mode)
        (hv : Work.BoseB7.FSParamsView E),
        hv.t ≤ t₀ → b₀ ≤ E.b → Work.BoseC3QAll.Q3KernelFSAll K₀ F T E →
        ∀ Φ : F.H, T.NWindow E.bigM Φ →
          ∑ k ∈ F.PHset E, (E.z / E.ell ^ 3) ^ 2 * (Work.BoseC3QAll.Est1.cD E k)⁻¹ *
              Work.BoseC3QAll.Est1.T2OpF F T E k Φ
            ≤ C * Work.BoseC3QAll.e1A E * F.normSq Φ
              + (E.b / 400) * F.qw Φ (T.gapOpT E)
              + (E.lille ^ 2 / 8) * F.qw Φ (F.dNumOpR E (F.PHq E.KH E.aScat)) := by
  obtain ⟨t_kb, ht_kb, Hkb⟩ := kernel_basic K₀ b₀ hb₀
  obtain ⟨t_ph, ht_ph, Hph⟩ := PH_subset_PHq_sub K₀ b₀ hb₀
  obtain ⟨t_hf, ht_hf, Hhf⟩ := fsXp_le_of_pos_exp (A := (97 : ℝ)) (c := (1 / 2 : ℝ))
      (by norm_num) (by norm_num)
  obtain ⟨t_ka, ht_ka, Hka⟩ := OpZ_kappa K₀ b₀ hb₀
  obtain ⟨t_at, ht_at, Hat⟩ := OpZ_Atil_sum K₀ b₀ hb₀
  obtain ⟨t_cd, ht_cd, Hcd⟩ := OpZ_cD_bd K₀ b₀ hb₀
  obtain ⟨t_rs, ht_rs, Hrs⟩ := OpZ_reserve K₀ b₀ hb₀
  obtain ⟨t_re, ht_re, Hre⟩ := OpZ_RE1 K₀ b₀ hb₀
  obtain ⟨C, hC0, HBt⟩ := OpZ_Bterm K₀ b₀ hb₀
  refine ⟨C, min t_kb (min t_ph (min t_hf (min t_ka (min t_at
      (min t_cd (min t_rs t_re)))))), hC0, ?_, ?_⟩
  · exact lt_min ht_kb (lt_min ht_ph (lt_min ht_hf (lt_min ht_ka
      (lt_min ht_at (lt_min ht_cd (lt_min ht_rs ht_re))))))
  · intro Mode _ _ _ F T E hv ht hb hK Φ hΦ
    rw [le_min_iff] at ht; obtain ⟨ht_kb, ht⟩ := ht
    rw [le_min_iff] at ht; obtain ⟨ht_ph, ht⟩ := ht
    rw [le_min_iff] at ht; obtain ⟨ht_hf, ht⟩ := ht
    rw [le_min_iff] at ht; obtain ⟨ht_ka, ht⟩ := ht
    rw [le_min_iff] at ht; obtain ⟨ht_at, ht⟩ := ht
    rw [le_min_iff] at ht; obtain ⟨ht_cd, ht⟩ := ht
    rw [le_min_iff] at ht; obtain ⟨ht_rs, ht_re⟩ := ht
    obtain ⟨hαeven, hAB, hhalf, hαle, hD4⟩ := Hkb F T E hv ht_kb hb hK
    obtain ⟨hPHsub, hsub, -⟩ := Hph F T E hv ht_ph hb hK
    have hell : 0 < E.ell := ell_pos E hv
    have hMnn : 0 ≤ E.bigM := le_trans zero_le_one hv.one_le_bigM
    have hDnn : ∀ q, 0 ≤ E.D q := fun q => FockData.Dcoef_nonneg (hK.AB q)
    have hlilsq : E.lille ^ 2 ≤ 1 / 2 := by
      have h1 : E.lille = Work.BoseBox.fsXp hv.t (97 / 2) := errA_lille E hv
      have h2 : (Work.BoseBox.fsXp hv.t (97 / 2)) ^ 2 = Work.BoseBox.fsXp hv.t 97 := by
        rw [Work.BoseBox.fsXp_pow hv.t_pos.le]
        norm_num
      rw [h1, h2]
      exact Hhf hv.t hv.t_pos ht_hf
    have hZ : (E.z / E.ell ^ 3) ^ 2 = E.rho / E.ell ^ 3 := z_div_ell_cube_sq hell.ne'
    have hcDnn : ∀ k, 0 ≤ cD E k := fun k => by
      rw [cD]
      exact mul_nonneg (by linarith [lille_sq_le_one E hv]) (hDnn k)
    have hZknn : ∀ k, 0 ≤ (E.z / E.ell ^ 3) ^ 2 * (cD E k)⁻¹ * E.W1 k ^ 2 := fun k =>
      mul_nonneg (mul_nonneg (sq_nonneg _) (inv_nonneg.mpr (hcDnn k))) (sq_nonneg _)
    have hq3nn : ∀ k s, 0 ≤ E.q3Denom s k := fun k s => by
      rw [Q3Env.q3Denom]
      exact div_nonneg zero_le_one (mul_nonneg (one_sub_alpha_sq_nonneg E k (hK.AB k))
        (one_sub_alpha_sq_nonneg E (s - k) (hK.AB (s - k))))
    -- **the guard of the corrected gate**: only modes with `Ŵ₁ k ≠ 0` admit the
    -- region fact `s − k ∈ P_H^q`, so every `k`-sum is restricted to them; nothing
    -- is lost because each summand carries a factor `Ŵ₁(k)` (or `Ŵ₁(k)²`).
    set Ke : Finset Mode := (F.PHset E).filter (fun k => E.W1 k ≠ 0) with hKe
    have hmemKe : ∀ k ∈ Ke, k ∈ F.PHset E ∧ E.W1 k ≠ 0 := fun k hk =>
      Finset.mem_filter.mp (hKe ▸ hk)
    have hT2OpF_zero : ∀ k, E.W1 k = 0 → T2OpF F T E k Φ = 0 := by
      intro k hW
      rw [T2OpF]
      refine Finset.sum_eq_zero fun s _ => Finset.sum_eq_zero fun s' _ => ?_
      simp only [gA, hW, mul_zero, zero_mul]
    have hq3le : ∀ k ∈ Ke, ∀ s, E.fL s ≠ 0 → E.q3Denom s k ≤ 4 := by
      intro k hk s hs
      obtain ⟨hkPH, hkW⟩ := hmemKe k hk
      have h1 : (1 : ℝ) / 2 ≤ 1 - E.alpha k ^ 2 :=
        hhalf k (hPHsub k (Finset.mem_filter.mp hkPH).2)
      have h2 : (1 : ℝ) / 2 ≤ 1 - E.alpha (s - k) ^ 2 :=
        hhalf (s - k) (hsub s k hs hkPH hkW)
      have hden : 0 < (1 - E.alpha k ^ 2) * (1 - E.alpha (s - k) ^ 2) := by nlinarith
      rw [Q3Env.q3Denom, div_le_iff₀ hden]
      nlinarith
    have hperK : ∀ k ∈ Ke, T2OpF F T E k Φ ≤ E.W1 k ^ 2 *
        (32 * (E.bigM + 1 + K₀ * (E.Kl * E.KL) ^ 3) *
            (∑ s' ∈ excited Mode,
              E.fL s' * E.q3Denom s' k * F.normSq (F.bOp E.alpha (s' - k) Φ))
          + 32 * (K₀ * (E.Kl * E.KL) ^ 3) ^ 2
              * (128 * K₀ ^ 2 * E.lille * Work.BoseC3QAll.eta E) ^ 2 * F.normSq Φ) := by
      intro k hk
      obtain ⟨hkPH, hkW⟩ := hmemKe k hk
      exact OpZ_perK F T E hΦ hMnn hK.fL_nonneg (fun s => hq3nn k s)
        (sum_fL_mul_le F E k _ hK.fL_nonneg hK.fL_le_one hK.count_PL
          (fun s hs => hq3le k hk s hs) (fun s _ => hq3nn k s))
        (fun s s' hs hs' =>
          Hka F T E hv ht_ka hb hK s k (s' - k) hs hkPH hkW (hsub s' k hs' hkPH hkW))
        (fun v hv' => Hat F T E hv ht_at hb hK k hkPH hkW v hv')
    set Z2 : ℝ := (E.z / E.ell ^ 3) ^ 2 with hZ2
    set κm : ℝ := 128 * K₀ ^ 2 * E.lille * Work.BoseC3QAll.eta E with hκm
    set A₀ : ℝ := K₀ * (E.Kl * E.KL) ^ 3 with hA₀
    set U : Mode → ℝ := fun k => ∑ s' ∈ excited Mode,
      E.fL s' * E.q3Denom s' k * F.normSq (F.bOp E.alpha (s' - k) Φ) with hU
    set Zk : Mode → ℝ := fun k => Z2 * (cD E k)⁻¹ * E.W1 k ^ 2 with hZk
    set Resv : ℝ := F.qw Φ (F.dNumOpR E (F.PHq E.KH E.aScat)) with hResv
    have hrestrict : ∑ k ∈ F.PHset E, Z2 * (cD E k)⁻¹ * T2OpF F T E k Φ
        = ∑ k ∈ Ke, Z2 * (cD E k)⁻¹ * T2OpF F T E k Φ := by
      rw [hKe]
      refine (Finset.sum_subset (Finset.filter_subset _ _) ?_).symm
      intro k hk hnot
      have hW : E.W1 k = 0 := by
        by_contra hne
        exact hnot (Finset.mem_filter.mpr ⟨hk, hne⟩)
      rw [hT2OpF_zero k hW]
      ring
    have hA₀nn : 0 ≤ A₀ := by
      rw [hA₀]
      exact mul_nonneg (K₀_nonneg_of_kernel K₀ F T E hv hK)
        (pow_nonneg (le_of_lt (mul_pos (lt_of_lt_of_le zero_lt_one hv.one_le_Kl)
          (lt_of_lt_of_le zero_lt_one hv.one_le_KL))) 3)
    have hZknn' : ∀ k, 0 ≤ Zk k := fun k => by rw [hZk, hZ2]; exact hZknn k
    have hResvnn : 0 ≤ Resv := by
      rw [hResv]; exact reserve_nonneg F E hK.AB Φ
    have hsum1 : (∑ k ∈ Ke, Z2 * (cD E k)⁻¹ * T2OpF F T E k Φ)
        ≤ ∑ k ∈ Ke, Zk k *
            (32 * (E.bigM + 1 + A₀) * U k + 32 * A₀ ^ 2 * κm ^ 2 * F.normSq Φ) := by
      refine Finset.sum_le_sum fun k hk => ?_
      have h1 := hperK k hk
      have hnn : 0 ≤ Z2 * (cD E k)⁻¹ := by
        rw [hZ2]; exact mul_nonneg (sq_nonneg _) (inv_nonneg.mpr (hcDnn k))
      have h2 : Z2 * (cD E k)⁻¹ * T2OpF F T E k Φ ≤
          Z2 * (cD E k)⁻¹ * (E.W1 k ^ 2 * (32 * (E.bigM + 1 + A₀) * U k
            + 32 * A₀ ^ 2 * κm ^ 2 * F.normSq Φ)) := mul_le_mul_of_nonneg_left h1 hnn
      calc Z2 * (cD E k)⁻¹ * T2OpF F T E k Φ
          ≤ Z2 * (cD E k)⁻¹ * (E.W1 k ^ 2 * (32 * (E.bigM + 1 + A₀) * U k
              + 32 * A₀ ^ 2 * κm ^ 2 * F.normSq Φ)) := h2
        _ = Zk k * (32 * (E.bigM + 1 + A₀) * U k + 32 * A₀ ^ 2 * κm ^ 2 * F.normSq Φ) := by
            rw [hZk]; ring
    have hsplit : (∑ k ∈ Ke, Zk k *
            (32 * (E.bigM + 1 + A₀) * U k + 32 * A₀ ^ 2 * κm ^ 2 * F.normSq Φ))
        = 32 * (E.bigM + 1 + A₀) * (∑ k ∈ Ke, Zk k * U k)
          + 32 * A₀ ^ 2 * κm ^ 2 * F.normSq Φ * (∑ k ∈ Ke, Zk k) := by
      simp only [mul_add, Finset.sum_add_distrib]
      congr 1
      · rw [Finset.mul_sum]
        exact Finset.sum_congr rfl fun k _ => by ring
      · rw [Finset.mul_sum]
        exact Finset.sum_congr rfl fun k _ => by ring
    have hSZ : (∑ k ∈ Ke, Zk k * U k) ≤ 8192 * K₀ ^ 3 * (E.Kl * E.KL) ^ 3
        * E.KH ^ 4 * E.aScat ^ 6 * Z2 * Resv := by
      have hstep1 : ∑ k ∈ Ke, Zk k * U k
          ≤ ∑ k ∈ Ke, Zk k * (∑ s' ∈ excited Mode,
              4 * (E.fL s' * F.normSq (F.bOp E.alpha (s' - k) Φ))) := by
        refine Finset.sum_le_sum fun k hk => ?_
        refine mul_le_mul_of_nonneg_left ?_ (hZknn' k)
        rw [hU]
        refine Finset.sum_le_sum fun s' _ => ?_
        rcases eq_or_lt_of_le (hK.fL_nonneg s') with h0 | h0
        · rw [← h0]; simp
        · have h1 := hq3le k hk s' (ne_of_gt h0)
          have hns : (0:ℝ) ≤ F.normSq (F.bOp E.alpha (s' - k) Φ) := F.bp_nonneg _
          calc E.fL s' * E.q3Denom s' k * F.normSq (F.bOp E.alpha (s' - k) Φ)
              ≤ E.fL s' * 4 * F.normSq (F.bOp E.alpha (s' - k) Φ) :=
                mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left h1 (le_of_lt h0)) hns
            _ = 4 * (E.fL s' * F.normSq (F.bOp E.alpha (s' - k) Φ)) := by ring
      have hstep2 : (∑ k ∈ Ke, Zk k * (∑ s' ∈ excited Mode,
              4 * (E.fL s' * F.normSq (F.bOp E.alpha (s' - k) Φ))))
          = ∑ s' ∈ excited Mode, 4 * (E.fL s' * (∑ k ∈ Ke,
              Zk k * F.normSq (F.bOp E.alpha (s' - k) Φ))) := by
        simp only [Finset.mul_sum]
        rw [Finset.sum_comm]
        exact Finset.sum_congr rfl fun s' _ => Finset.sum_congr rfl fun k _ => by ring
      have hstep3 : ∑ s' ∈ excited Mode, 4 * (E.fL s' * (∑ k ∈ Ke,
              Zk k * F.normSq (F.bOp E.alpha (s' - k) Φ)))
          ≤ ∑ s' ∈ excited Mode, 4 * (E.fL s' *
              (Z2 * (2048 * K₀ ^ 2 * E.KH ^ 4 * E.aScat ^ 6) * Resv)) := by
        refine Finset.sum_le_sum fun s' _ => ?_
        by_cases hs : E.fL s' = 0
        · rw [hs]; simp
        · refine mul_le_mul_of_nonneg_left ?_ (by norm_num)
          refine mul_le_mul_of_nonneg_left ?_ (hK.fL_nonneg s')
          calc ∑ k ∈ Ke, Zk k * F.normSq (F.bOp E.alpha (s' - k) Φ)
              ≤ ∑ k ∈ Ke, (Z2 * (2048 * K₀ ^ 2 * E.KH ^ 4 * E.aScat ^ 6)
                  * E.D (s' - k)) * F.normSq (F.bOp E.alpha (s' - k) Φ) := by
                refine Finset.sum_le_sum fun k hk => ?_
                have hcd := Hcd F T E hv ht_cd hb hK s' k hs (hmemKe k hk).1
                refine mul_le_mul_of_nonneg_right ?_
                  (F.bp_nonneg (F.bOp E.alpha (s' - k) Φ))
                rw [hZk, hZ2]
                calc (E.z / E.ell ^ 3) ^ 2 * (cD E k)⁻¹ * E.W1 k ^ 2
                    = (E.z / E.ell ^ 3) ^ 2 * ((cD E k)⁻¹ * E.W1 k ^ 2) := by ring
                  _ ≤ (E.z / E.ell ^ 3) ^ 2
                        * (2048 * K₀ ^ 2 * E.KH ^ 4 * E.aScat ^ 6 * E.D (s' - k)) :=
                      mul_le_mul_of_nonneg_left hcd (sq_nonneg _)
                  _ = (E.z / E.ell ^ 3) ^ 2 * (2048 * K₀ ^ 2 * E.KH ^ 4 * E.aScat ^ 6)
                        * E.D (s' - k) := by ring
            _ = Z2 * (2048 * K₀ ^ 2 * E.KH ^ 4 * E.aScat ^ 6)
                  * (∑ k ∈ Ke, E.D (s' - k) * F.normSq (F.bOp E.alpha (s' - k) Φ)) := by
                rw [hZ2, Finset.mul_sum]
                exact Finset.sum_congr rfl fun k _ => by ring
            _ ≤ Z2 * (2048 * K₀ ^ 2 * E.KH ^ 4 * E.aScat ^ 6) * Resv := by
                refine mul_le_mul_of_nonneg_left ?_ (by positivity)
                have hrs := Hrs F T E hv ht_rs hb hK s' hs Φ
                have hconv : (∑ k ∈ (F.PHset E).filter (fun k => E.W1 k ≠ 0),
                      E.D (s' - k) * F.bp ((F.bNumOp E.alpha (s' - k)) Φ) Φ)
                    = ∑ k ∈ (F.PHset E).filter (fun k => E.W1 k ≠ 0),
                        E.D (s' - k) * F.normSq (F.bOp E.alpha (s' - k) Φ) :=
                  Finset.sum_congr rfl fun k _ => by rw [bNumOp_qw_eq]
                rw [hconv] at hrs
                rw [hResv]
                exact hrs
      have hstep4 : ∑ s' ∈ excited Mode, 4 * (E.fL s' *
              (Z2 * (2048 * K₀ ^ 2 * E.KH ^ 4 * E.aScat ^ 6) * Resv))
          = 4 * (∑ s' ∈ excited Mode, E.fL s')
              * (Z2 * (2048 * K₀ ^ 2 * E.KH ^ 4 * E.aScat ^ 6) * Resv) := by
        rw [Finset.mul_sum, Finset.sum_mul]
        exact Finset.sum_congr rfl fun s' _ => by ring
      have hstep5 : 4 * (∑ s' ∈ excited Mode, E.fL s')
              * (Z2 * (2048 * K₀ ^ 2 * E.KH ^ 4 * E.aScat ^ 6) * Resv)
          ≤ 4 * A₀ * (Z2 * (2048 * K₀ ^ 2 * E.KH ^ 4 * E.aScat ^ 6) * Resv) := by
        have hcoefnn : (0:ℝ) ≤ Z2 * (2048 * K₀ ^ 2 * E.KH ^ 4 * E.aScat ^ 6) * Resv := by
          rw [hZ2]
          have hK₀0 : (0:ℝ) ≤ K₀ := K₀_nonneg_of_kernel K₀ F T E hv hK
          have hKH0 : (0:ℝ) ≤ E.KH := le_of_lt (lt_of_lt_of_le zero_lt_one hv.one_le_KH)
          have ha0 : (0:ℝ) ≤ E.aScat := le_of_lt hv.a_pos
          exact mul_nonneg (mul_nonneg (sq_nonneg _) (by positivity)) hResvnn
        have hf : ∑ s' ∈ excited Mode, E.fL s' ≤ A₀ := by
          rw [hA₀]
          exact sum_fL_le F E _ hK.fL_nonneg hK.fL_le_one hK.count_PL
        exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hf (by norm_num)) hcoefnn
      calc ∑ k ∈ Ke, Zk k * U k
          ≤ ∑ k ∈ Ke, Zk k * (∑ s' ∈ excited Mode,
              4 * (E.fL s' * F.normSq (F.bOp E.alpha (s' - k) Φ))) := hstep1
        _ = ∑ s' ∈ excited Mode, 4 * (E.fL s' * (∑ k ∈ Ke,
              Zk k * F.normSq (F.bOp E.alpha (s' - k) Φ))) := hstep2
        _ ≤ ∑ s' ∈ excited Mode, 4 * (E.fL s' *
              (Z2 * (2048 * K₀ ^ 2 * E.KH ^ 4 * E.aScat ^ 6) * Resv)) := hstep3
        _ = 4 * (∑ s' ∈ excited Mode, E.fL s')
              * (Z2 * (2048 * K₀ ^ 2 * E.KH ^ 4 * E.aScat ^ 6) * Resv) := hstep4
        _ ≤ 4 * A₀ * (Z2 * (2048 * K₀ ^ 2 * E.KH ^ 4 * E.aScat ^ 6) * Resv) := hstep5
        _ = 8192 * K₀ ^ 3 * (E.Kl * E.KL) ^ 3 * E.KH ^ 4 * E.aScat ^ 6 * Z2 * Resv := by
            rw [hA₀]; ring
    have hSk : (∑ k ∈ Ke, Zk k) ≤ 8 * E.rho * K₀ * E.aScat := by
      rw [hZk, hZ2]
      refine sum_cD_W1sq_subset F E K₀ Ke hell ?_ ?_ ?_ ?_ hK.sum_W1sq
      · exact z_div_ell_cube_sq hell.ne'
      · intro k hk
        exact (hmemKe k hk).1
      · intro k hk
        have hk' : F.PHq E.KH E.aScat k :=
          hPHsub k (Finset.mem_filter.mp (hmemKe k hk).1).2
        have hDk : ‖F.kmom k‖ ^ 2 / 4 ≤ E.D k := hD4 k hk'
        have hcut : 1 / (4 * E.KH * E.aScat) ≤ ‖F.kmom k‖ := hk'
        have hcutpos : 0 < 1 / (4 * E.KH * E.aScat) := by
          apply one_div_pos.mpr
          have h1 : (0:ℝ) < E.KH := lt_of_lt_of_le zero_lt_one hv.one_le_KH
          have h2 : (0:ℝ) < E.aScat := hv.a_pos
          positivity
        have hkmpos : 0 < ‖F.kmom k‖ := lt_of_lt_of_le hcutpos hcut
        have hDq : (0:ℝ) < ‖F.kmom k‖ ^ 2 / 4 := div_pos (pow_pos hkmpos 2) (by norm_num)
        have hDpos : 0 < E.D k := by linarith [hDk, hDq]
        have hcl : (1 : ℝ) / 2 ≤ 1 - E.lille ^ 2 := by linarith [hlilsq]
        have hcD2 : (1 : ℝ) / 2 * E.D k ≤ cD E k := by
          rw [cD]; nlinarith
        have hden2 : (0 : ℝ) < (1/2) * E.D k := by positivity
        have hstep1 : (cD E k)⁻¹ ≤ 2 / E.D k := by
          calc (cD E k)⁻¹ = 1 / cD E k := by rw [one_div]
            _ ≤ 1 / ((1/2) * E.D k) := one_div_le_one_div_of_le hden2 hcD2
            _ = 2 / E.D k := by field_simp
        have hstep2 : (2 : ℝ) / E.D k ≤ 8 / ‖F.kmom k‖ ^ 2 := by
          rw [div_le_iff₀ hDpos]
          rw [show (8 / ‖F.kmom k‖ ^ 2) * E.D k = 8 * E.D k / ‖F.kmom k‖ ^ 2 by ring]
          rw [le_div_iff₀ (pow_pos hkmpos 2)]
          nlinarith [hDk]
        have hfin : (cD E k)⁻¹ ≤ 8 / ‖F.kmom k‖ ^ 2 := le_trans hstep1 hstep2
        calc (cD E k)⁻¹ * E.W1 k ^ 2 ≤ (8 / ‖F.kmom k‖ ^ 2) * E.W1 k ^ 2 :=
              mul_le_mul_of_nonneg_right hfin (sq_nonneg _)
          _ = 8 * E.W1 k ^ 2 / ‖F.kmom k‖ ^ 2 := by ring
      · intro k hk
        exact hPHsub k (Finset.mem_filter.mp (hmemKe k hk).1).2
    have hfin : (∑ k ∈ Ke, Z2 * (cD E k)⁻¹ * T2OpF F T E k Φ)
        ≤ 32 * (E.bigM + 1 + A₀) * (8192 * K₀ ^ 3 * (E.Kl * E.KL) ^ 3
              * E.KH ^ 4 * E.aScat ^ 6 * Z2 * Resv)
          + 32 * A₀ ^ 2 * κm ^ 2 * F.normSq Φ * (8 * E.rho * K₀ * E.aScat) := by
      have h1 : 32 * (E.bigM + 1 + A₀) * (∑ k ∈ Ke, Zk k * U k)
          ≤ 32 * (E.bigM + 1 + A₀) * (8192 * K₀ ^ 3 * (E.Kl * E.KL) ^ 3
              * E.KH ^ 4 * E.aScat ^ 6 * Z2 * Resv) := by
        exact mul_le_mul_of_nonneg_left hSZ (mul_nonneg (by norm_num) (by linarith [hMnn, hA₀nn]))
      have h2 : 32 * A₀ ^ 2 * κm ^ 2 * F.normSq Φ * (∑ k ∈ Ke, Zk k)
          ≤ 32 * A₀ ^ 2 * κm ^ 2 * F.normSq Φ * (8 * E.rho * K₀ * E.aScat) := by
        exact mul_le_mul_of_nonneg_left hSk
          (mul_nonneg (mul_nonneg (mul_nonneg (by norm_num) (sq_nonneg A₀)) (sq_nonneg κm))
            (F.bp_nonneg Φ))
      linarith [hsum1, hsplit, h1, h2]
    have hA : 32 * (E.bigM + 1 + A₀) * (8192 * K₀ ^ 3 * (E.Kl * E.KL) ^ 3
            * E.KH ^ 4 * E.aScat ^ 6 * Z2 * Resv)
        ≤ (E.lille ^ 2 / 8) * Resv := by
      have hre := Hre F T E hv ht_re hb hK
      have heq : 32 * (E.bigM + 1 + A₀) * (8192 * K₀ ^ 3 * (E.Kl * E.KL) ^ 3
            * E.KH ^ 4 * E.aScat ^ 6 * Z2 * Resv)
          = (262144 * K₀ ^ 3 * (E.Kl * E.KL) ^ 3 * E.KH ^ 4 * E.aScat ^ 6
              * (E.z / E.ell ^ 3) ^ 2 * (E.bigM + 1 + K₀ * (E.Kl * E.KL) ^ 3)) * Resv := by
        rw [hZ2, hA₀]; ring
      rw [heq]
      exact mul_le_mul_of_nonneg_right hre hResvnn
    have hB : 32 * A₀ ^ 2 * κm ^ 2 * F.normSq Φ * (8 * E.rho * K₀ * E.aScat)
        ≤ C * e1A E * F.normSq Φ := by
      have hbt := HBt F T E hv hb hK
      have heq : 32 * A₀ ^ 2 * κm ^ 2 * F.normSq Φ * (8 * E.rho * K₀ * E.aScat)
          = (4194304 * E.rho * K₀ ^ 7 * E.aScat * (E.Kl * E.KL) ^ 6 * E.lille ^ 2
              * eta E ^ 2) * F.normSq Φ := by
        rw [hA₀, hκm]; ring
      rw [heq]
      exact mul_le_mul_of_nonneg_right hbt (F.bp_nonneg Φ)
    have hgapnn : 0 ≤ (E.b / 400) * F.qw Φ (T.gapOpT E) :=
      mul_nonneg (by have := b_pos_of_le hb₀ hb; positivity) (gapOpT_qw_nonneg_local F T E hv Φ)
    have hresnn : 0 ≤ (E.lille ^ 2 / 8) * Resv :=
      mul_nonneg (by positivity) hResvnn
    rw [hrestrict]
    linarith [hfin, hA, hB, hgapnn, hresnn]

end Est1

end Work.BoseC3QAll
