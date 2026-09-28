import Mathlib
import Submission.Work.HP.Defs
import Submission.Work.HP.Vero.SigmaDefs
import Submission.Work.HP.Vero.SecondCaseDefs
import Submission.Work.HP.Vero.SigmaLinalg
import Submission.Work.HP.Vero.span_realify_latOrth_inf

set_option autoImplicit false

namespace Work.HP.Vero

/-! ### The coordinate formula for `pairMon` -/

lemma pairMon_val (n : ℕ) (i j r : Fin (n + 1)) :
    ((pairMon n i j).1 r).val = (if r = i then 1 else 0) + (if r = j then 1 else 0) := by
  simp [pairMon, Work.HP.NA.monDij]

/-! ### Every degree-two monomial is `XᵢXⱼ` -/

lemma pairMon_cover {n : ℕ} (m : Mon 2 n) : ∃ i j : Fin (n + 1), pairMon n i j = m := by
  classical
  obtain ⟨f, hf⟩ := m
  by_cases h2 : ∃ i : Fin (n + 1), (f i).val = 2
  · obtain ⟨i, hi⟩ := h2
    have hzero : ∀ r, r ≠ i → (f r).val = 0 := by
      intro r hr
      have h1 := Finset.sum_erase_add Finset.univ (fun t => (f t).val) (Finset.mem_univ i)
      rw [hi] at h1
      have h0 : ∑ t ∈ Finset.univ.erase i, (f t).val = 0 := by omega
      exact (Finset.sum_eq_zero_iff_of_nonneg (fun t _ => Nat.zero_le _)).mp h0 r
        (Finset.mem_erase.mpr ⟨hr, Finset.mem_univ r⟩)
    refine ⟨i, i, ?_⟩
    apply Subtype.ext; funext r; apply Fin.ext
    rw [pairMon_val]
    by_cases hr : r = i
    · rw [if_pos hr, hr, hi]
    · rw [if_neg hr, hzero r hr]
  · push Not at h2
    have hp1 : ∀ r, (f r).val ≤ 1 := by intro r; have := h2 r; omega
    have hne : (∑ t : Fin (n + 1), (f t).val) ≠ 0 := by rw [hf]; norm_num
    obtain ⟨i, _, hi⟩ := Finset.exists_ne_zero_of_sum_ne_zero hne
    have hvi : (f i).val = 1 := by have := hp1 i; omega
    have hsumI : ∑ t ∈ Finset.univ.erase i, (f t).val = 1 := by
      have h1 := Finset.sum_erase_add Finset.univ (fun t => (f t).val) (Finset.mem_univ i)
      rw [hvi, hf] at h1; omega
    have hne3 : (∑ t ∈ Finset.univ.erase i, (f t).val) ≠ 0 := by rw [hsumI]; norm_num
    obtain ⟨j, hjmem, hj⟩ := Finset.exists_ne_zero_of_sum_ne_zero hne3
    have hvj : (f j).val = 1 := by have := hp1 j; omega
    have hji : j ≠ i := (Finset.mem_erase.mp hjmem).1
    have hzero2 : ∀ r, r ≠ i → r ≠ j → (f r).val = 0 := by
      intro r hri hrj
      have h1 := Finset.sum_erase_add (Finset.univ.erase i) (fun t => (f t).val) hjmem
      rw [hvj, hsumI] at h1
      have h0 : ∑ t ∈ (Finset.univ.erase i).erase j, (f t).val = 0 := by omega
      exact (Finset.sum_eq_zero_iff_of_nonneg (fun t _ => Nat.zero_le _)).mp h0 r
        (Finset.mem_erase.mpr ⟨hrj, Finset.mem_erase.mpr ⟨hri, Finset.mem_univ r⟩⟩)
    refine ⟨i, j, ?_⟩
    apply Subtype.ext; funext r; apply Fin.ext
    rw [pairMon_val]
    by_cases hri : r = i
    · rw [hri, if_pos rfl, if_neg (Ne.symm hji), hvi]
    · by_cases hrj : r = j
      · rw [hrj, if_neg hji, if_pos rfl, hvj]
      · rw [if_neg hri, if_neg hrj, hzero2 r hri hrj]

/-! ### A nonzero `2×2` minor from linear independence -/

lemma exists_minor_ne_zero {n : ℕ} (x y : Fin (n + 1) → ℝ)
    (hxy : LinearIndependent ℝ ![x, y]) :
    ∃ p q : Fin (n + 1), x p * y q - x q * y p ≠ 0 := by
  by_contra h
  push Not at h
  have hxne : x ≠ 0 := by
    intro hx
    have h0 : (1:ℝ) • x + (0:ℝ) • y = 0 := by rw [hx]; simp
    exact one_ne_zero (LinearIndependent.pair_iff.mp hxy 1 0 h0).1
  obtain ⟨p, hp⟩ : ∃ p, x p ≠ 0 := by
    by_contra hc; push Not at hc
    exact hxne (funext hc)
  set lam : ℝ := y p / x p with hlam
  have hy : y = lam • x := by
    funext q
    simp only [Pi.smul_apply, smul_eq_mul, hlam]
    have hq : x p * y q = x q * y p := by linarith [h p q]
    field_simp
    nlinarith [hq]
  have hrel : (-lam) • x + (1:ℝ) • y = 0 := by
    rw [hy, one_smul, ← add_smul, neg_add_cancel, zero_smul]
  exact one_ne_zero (LinearIndependent.pair_iff.mp hxy (-lam) 1 hrel).2

/-! ### A symmetric matrix with rows in a 2-dimensional span -/

lemma exists_coeffs_of_symm_rows {n : ℕ} (x y : Fin (n + 1) → ℝ)
    (B : Fin (n + 1) → Fin (n + 1) → ℝ)
    (hxy : LinearIndependent ℝ ![x, y])
    (hsym : ∀ i j, B i j = B j i)
    (hrows : ∀ i, (fun j => B i j) ∈ Submodule.span ℝ ({x, y} : Set (Fin (n + 1) → ℝ))) :
    ∃ α β γ : ℝ, ∀ i j,
      B i j = α * x i * x j + β * y i * y j + γ * (x i * y j + y i * x j) := by
  classical
  choose c d hcd using fun i => Submodule.mem_span_pair.mp (hrows i)
  have hcd' : ∀ i j, B i j = c i * x j + d i * y j := by
    intro i j
    have h := congrFun (hcd i) j
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul] at h
    linarith [h]
  obtain ⟨p, q, hpq⟩ := exists_minor_ne_zero x y hxy
  set D := x p * y q - x q * y p with hD
  have hDne : D ≠ 0 := hpq
  have hrel : ∀ i j, c i * x j + d i * y j = c j * x i + d j * y i := by
    intro i j
    rw [← hcd' i j, ← hcd' j i]
    exact hsym i j
  have hgam : (x p * c q - x q * c p) / D = (d p * y q - d q * y p) / D := by
    have h := hrel p q
    have h2 : x p * c q - x q * c p = d p * y q - d q * y p := by linarith [h]
    rw [h2]
  refine ⟨(c p * y q - c q * y p)/D, (x p * d q - x q * d p)/D,
      (d p * y q - d q * y p)/D, ?_⟩
  intro i j
  have hci : c i = (c p * y q - c q * y p)/D * x i + (d p * y q - d q * y p)/D * y i := by
    have e1 := hrel p i
    have e2 := hrel q i
    have key : c i * D = (c p * y q - c q * y p) * x i + (d p * y q - d q * y p) * y i := by
      have h : (c p * x i + d p * y i) * y q - (c q * x i + d q * y i) * y p = c i * D := by
        rw [e1, e2, hD]; ring
      rw [← h]; ring
    have hgoal : c i = ((c p * y q - c q * y p) * x i + (d p * y q - d q * y p) * y i)/D := by
      rw [eq_div_iff hDne]; exact key
    rw [hgoal]
    ring_nf
  have hdi : d i = (d p * y q - d q * y p)/D * x i + (x p * d q - x q * d p)/D * y i := by
    have e1 := hrel p i
    have e2 := hrel q i
    have key : d i * D = (c q * x p - c p * x q) * x i + (d q * x p - d p * x q) * y i := by
      have h : (c p * x i + d p * y i) * x q - (c q * x i + d q * y i) * x p = -(d i * D) := by
        rw [e1, e2, hD]; ring
      have h2 : d i * D = -((c p * x i + d p * y i) * x q - (c q * x i + d q * y i) * x p) := by
        rw [h]; ring
      rw [h2]; ring
    have hgam' : (d p * y q - d q * y p) / D = (c q * x p - c p * x q) / D := by
      rw [← hgam]; congr 1; ring
    have hgoal : d i = ((c q * x p - c p * x q) * x i + (d q * x p - d p * x q) * y i)/D := by
      rw [eq_div_iff hDne]; exact key
    rw [hgoal, hgam']
    ring_nf
  rw [hcd' i j, hci, hdi]
  ring_nf

/-! ### Integer orthogonality and the span of two vectors -/

lemma sum_single_mul_gen {ι : Type*} [Fintype ι] [DecidableEq ι] {R : Type*} [Semiring R]
    (a : ι) (c : R) (f : ι → R) :
    ∑ i, (Pi.single a c : ι → R) i * f i = c * f a := by
  rw [Finset.sum_eq_single a]
  · simp
  · intro b _ hb; rw [Pi.single_eq_of_ne hb, zero_mul]
  · intro h; exact absurd (Finset.mem_univ a) h

lemma sum_three_singles_mul {ι : Type*} [Fintype ι] [DecidableEq ι] {R : Type*} [Semiring R]
    (p q r : ι) (A B C : R) (f : ι → R) :
    ∑ i, ((Pi.single p A + Pi.single q B + Pi.single r C : ι → R)) i * f i
      = A * f p + B * f q + C * f r := by
  simp only [Pi.add_apply, add_mul, Finset.sum_add_distrib, sum_single_mul_gen]

lemma mem_span_pair_of_int_orthogonal {n : ℕ} (x y : Fin (n + 1) → ℤ) (z : Fin (n + 1) → ℝ)
    (hxy : LinearIndependent ℝ ![toR x, toR y])
    (h : ∀ v : Fin (n + 1) → ℤ, (∑ j, v j * x j = 0) → (∑ j, v j * y j = 0) →
        ∑ j, z j * (v j : ℝ) = 0) :
    z ∈ Submodule.span ℝ ({toR x, toR y} : Set (Fin (n + 1) → ℝ)) := by
  classical
  obtain ⟨p, q, hpqD⟩ := exists_minor_ne_zero (toR x) (toR y) hxy
  have hpq : p ≠ q := by
    intro heq; rw [heq] at hpqD; simp at hpqD
  set D : ℝ := (x p : ℝ) * (y q : ℝ) - (x q : ℝ) * (y p : ℝ) with hDdef
  have hDne : D ≠ 0 := by rw [hDdef]; exact hpqD
  set c : ℝ := (z p * (y q : ℝ) - z q * (y p : ℝ)) / D with hc
  set d : ℝ := ((x p : ℝ) * z q - (x q : ℝ) * z p) / D with hd
  set z' : Fin (n + 1) → ℝ := z - c • (toR x) - d • (toR y) with hz'
  have hzp : z' p = 0 := by
    simp only [hz', Pi.sub_apply, Pi.smul_apply, smul_eq_mul, toR]
    rw [hc, hd]
    field_simp
    rw [hDdef]
    ring
  have hzq : z' q = 0 := by
    simp only [hz', Pi.sub_apply, Pi.smul_apply, smul_eq_mul, toR]
    rw [hc, hd]
    field_simp
    rw [hDdef]
    ring
  have hzr : ∀ r : Fin (n + 1), r ≠ p → r ≠ q → z' r = 0 := by
    intro r hrp hrq
    set A : ℤ := x q * y r - x r * y q with hA
    set B : ℤ := x r * y p - x p * y r with hB
    set Cc : ℤ := x p * y q - x q * y p with hC
    set v : Fin (n + 1) → ℤ := Pi.single p A + Pi.single q B + Pi.single r Cc with hv
    have hvx : ∑ i, v i * x i = 0 := by
      rw [hv, sum_three_singles_mul p q r A B Cc x, hA, hB, hC]; ring
    have hvy : ∑ i, v i * y i = 0 := by
      rw [hv, sum_three_singles_mul p q r A B Cc y, hA, hB, hC]; ring
    have hzv : ∑ i, z i * (v i : ℝ) = 0 := h v hvx hvy
    have hgen : ∀ f : Fin (n + 1) → ℝ,
        ∑ i, f i * (v i : ℝ) = (A : ℝ) * f p + (B : ℝ) * f q + (Cc : ℝ) * f r := by
      intro f
      have hvcast : ∀ i : Fin (n + 1), (v i : ℝ)
          = (Pi.single p (A:ℝ) + Pi.single q (B:ℝ) + Pi.single r (Cc:ℝ)
              : Fin (n+1) → ℝ) i := by
        intro i
        rw [hv]
        by_cases hip : i = p <;> by_cases hiq : i = q <;> by_cases hir : i = r <;>
          simp [hip, hiq, hir, hrp, hrq, hpq, Pi.add_apply]
      have hs : ∑ i, f i * (v i : ℝ)
          = ∑ i, f i * ((Pi.single p (A:ℝ) + Pi.single q (B:ℝ) + Pi.single r (Cc:ℝ)
              : Fin (n+1) → ℝ) i) :=
        Finset.sum_congr rfl (fun i _ => by rw [hvcast i])
      rw [hs, show ∑ i, f i * ((Pi.single p (A:ℝ) + Pi.single q (B:ℝ) + Pi.single r (Cc:ℝ)
              : Fin (n+1) → ℝ) i)
            = ∑ i, ((Pi.single p (A:ℝ) + Pi.single q (B:ℝ) + Pi.single r (Cc:ℝ)
              : Fin (n+1) → ℝ) i) * f i from
          Finset.sum_congr rfl (fun i _ => mul_comm _ _)]
      exact sum_three_singles_mul p q r (A:ℝ) (B:ℝ) (Cc:ℝ) f
    have hXv : ∑ i, (toR x) i * (v i : ℝ) = 0 := by
      simp only [toR]
      have hcast : ((∑ i, x i * v i : ℤ) : ℝ) = ∑ i, (x i : ℝ) * (v i : ℝ) := by push_cast; rfl
      rw [← hcast, show ∑ i, x i * v i = ∑ i, v i * x i from
        Finset.sum_congr rfl (fun i _ => mul_comm _ _), hvx]; simp
    have hYv : ∑ i, (toR y) i * (v i : ℝ) = 0 := by
      simp only [toR]
      have hcast : ((∑ i, y i * v i : ℤ) : ℝ) = ∑ i, (y i : ℝ) * (v i : ℝ) := by push_cast; rfl
      rw [← hcast, show ∑ i, y i * v i = ∑ i, v i * y i from
        Finset.sum_congr rfl (fun i _ => mul_comm _ _), hvy]; simp
    have hsum0 : ∑ i, z' i * (v i : ℝ) = 0 := by
      have e1 : ∑ i, z' i * (v i:ℝ)
          = ∑ i, (z i * (v i:ℝ) - c * ((toR x) i * (v i:ℝ))
              - d * ((toR y) i * (v i:ℝ))) := by
        rw [hz']
        refine Finset.sum_congr rfl (fun i _ => ?_)
        simp only [Pi.sub_apply, Pi.smul_apply, smul_eq_mul]; ring
      rw [e1, Finset.sum_sub_distrib, Finset.sum_sub_distrib, ← Finset.mul_sum,
        ← Finset.mul_sum, hzv, hXv, hYv]; ring
    have hCr : z' r * (Cc : ℝ) = 0 := by
      have h1 : ∑ i, z' i * (v i : ℝ) = z' r * (Cc : ℝ) := by
        rw [hgen z', hzp, hzq]; ring
      rw [← h1]; exact hsum0
    have hCcne : (Cc : ℝ) ≠ 0 := by
      have hCc : (Cc : ℝ) = D := by rw [hC, hDdef]; push_cast; ring
      rw [hCc]; exact hDne
    exact (mul_eq_zero.mp hCr).resolve_right hCcne
  have hz'0 : z' = 0 := funext (fun r => by
    by_cases hrp : r = p
    · rw [hrp]; exact hzp
    · by_cases hrq : r = q
      · rw [hrq]; exact hzq
      · exact hzr r hrp hrq)
  have hzeq : z = c • (toR x) + d • (toR y) := by
    have h0 : z - c • (toR x) - d • (toR y) = 0 := by rw [← hz']; exact hz'0
    rw [sub_sub, sub_eq_zero] at h0
    exact h0
  exact Submodule.mem_span_pair.mpr ⟨c, d, hzeq.symm⟩

/-! ### The main theorem -/

theorem second_case_witness {n : ℕ} (x y : Fin (n + 1) → ℤ) (hxy : LinearIndependent ℤ ![x, y])
    (a : Mon 2 n → ℝ)
    (ha : a ∉ Submodule.span ℝ ({toR (veronese 2 n x), toR (veronese 2 n y),
      toR (veronese 2 n (x + y))} : Set (Mon 2 n → ℝ))) :
    ∃ i : Fin (n + 1), ∃ v : Fin (n + 1) → ℤ,
      (∑ j, v j * x j = 0) ∧ (∑ j, v j * y j = 0) ∧
      (∑ m : Mon 2 n, a m * (sigma n (Pi.single i 1) v m : ℝ)) ≠ 0 := by
  classical
  by_contra hcon
  push Not at hcon
  have hxyR : LinearIndependent ℝ ![toR x, toR y] := by
    have h := linInd_intCastPi (b := ![x, y]) hxy
    rw [show (![toR x, toR y] : Fin 2 → (Fin (n + 1) → ℝ))
        = (fun j => Work.HP.intCastPi (![x, y] j)) from by
      funext j
      fin_cases j <;> rfl]
    exact h
  have hrows : ∀ i : Fin (n + 1),
      rowVecR n i a ∈ Submodule.span ℝ ({toR x, toR y} : Set (Fin (n + 1) → ℝ)) := by
    intro i
    refine mem_span_pair_of_int_orthogonal x y (rowVecR n i a) hxyR ?_
    intro v hvx hvy
    rw [← dot_sigma_rowVecR n i v a]
    exact hcon i v hvx hvy
  obtain ⟨α, β, γ, hαβγ⟩ := exists_coeffs_of_symm_rows (toR x) (toR y) (matA n a) hxyR
    (fun i j => matA_comm n a i j) (fun i => hrows i)
  have hmem : (α - γ) • (toR (veronese 2 n x)) + (β - γ) • (toR (veronese 2 n y))
      + γ • (toR (veronese 2 n (x + y)))
      ∈ Submodule.span ℝ ({toR (veronese 2 n x), toR (veronese 2 n y),
          toR (veronese 2 n (x + y))} : Set (Mon 2 n → ℝ)) := by
    refine Submodule.add_mem _ (Submodule.add_mem _ ?_ ?_) ?_
    · exact Submodule.smul_mem _ _ (Submodule.subset_span (by simp))
    · exact Submodule.smul_mem _ _ (Submodule.subset_span (by simp))
    · exact Submodule.smul_mem _ _ (Submodule.subset_span (by simp))
  have heq : a = (α - γ) • (toR (veronese 2 n x)) + (β - γ) • (toR (veronese 2 n y))
      + γ • (toR (veronese 2 n (x + y))) := by
    funext m
    obtain ⟨i, j, rfl⟩ := pairMon_cover m
    change matA n a i j = _
    rw [hαβγ i j]
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, toR, veronese_pairMon, Pi.add_apply]
    push_cast
    ring
  exact ha (by rw [heq]; exact hmem)

end Work.HP.Vero
