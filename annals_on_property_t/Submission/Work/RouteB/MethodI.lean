import Submission.Work.RouteB.SymCounting
import Submission.Work.RouteB.AutCertificate

open OnPropertyT Submission.FreeGroupAut Submission.Helpers
open scoped BigOperators

set_option autoImplicit false

/-!
# Method I: the symmetrisation of the certificate `Adj_n + k·Op_n − μ·Δ_n`

Kaluba–Kielak–Nowak, *Method I* (`Adj+kOp>=0`): a sum-of-squares certificate

    `Adj_n + k·Op_n − μ·Δ_n ∈ Σ²    (k ≥ 0, μ > 0)`

for the transvections of the sub-simplex on `n` vertices implies, for every
`m ≥ n` with `k(n−3) ≤ m−3`, the certificate

    `Δ_m² − (μ(m−2)/(n−2))·Δ_m ∈ Σ²`

for the transvections of the full `m`-vertex simplex, hence `PropertyT (Aut(F_m))`
by the index-two ascent `Submission.Nielsen.propertyT_aut_of_sAutGen_certificate''`.

The proof is the averaged identity (`sum_permRingHom_cert`, from the three
counting identities of `SymCounting.lean`)

    `(1/cAdj)·∑_σ σ(Adj_n + k·Op_n − μ·Δ_n)
        = Adj_m + k(cOp/cAdj)·Op_m − (μ cSq/cAdj)·Δ_m`,

which, together with `Δ_m² = Sq_m + Adj_m + Op_m`, cancels the `Adj_m` term
*exactly*:

    `Δ_m² − (μ cSq/cAdj)·Δ_m
        = Sq_m + (1 − k cOp/cAdj)·Op_m + (1/cAdj)·∑_σ σ(Adj_n + k·Op_n − μ·Δ_n)`.

All three summands are sums of hermitian squares (`isSOS_SqLap`, `isSOS_OpLap`
and `IsSOS.map`/`IsSOS.smul`), and the middle coefficient is nonnegative exactly
when `k·(n−3) ≤ m−3`.  Note that the `Adj_m` term — which is *not* known to be a
sum of squares — has cancelled; this is the point of the paper's arrangement.
-/

namespace Submission.RouteB

namespace Edge

variable {m : ℕ}

/-! ## Two elementary lemmas -/

/-- `permRingHom σ` is `ℝ`-linear (it is a ring homomorphism between real
algebras, hence respects the real scalars). -/
lemma permRingHom_smul (σ : Equiv.Perm (Fin m)) (r : ℝ)
    (x : MonoidAlgebra ℝ (MulAut (FreeGroup (Fin m)))) :
    permRingHom σ (r • x) = r • permRingHom σ x := by
  rw [permRingHom_eq_conj, permRingHom_eq_conj, mul_smul_comm, smul_mul_assoc]

/-- Scalar multiples of a finite sum. -/
lemma sum_smul_fintype {ι : Type*} [Fintype ι] (r : ℝ)
    (f : ι → MonoidAlgebra ℝ (MulAut (FreeGroup (Fin m)))) :
    (∑ i : ι, r • f i) = r • ∑ i : ι, f i :=
  (Finset.smul_sum (r := r) (f := f) (s := Finset.univ)).symm

/-- `k.choose 2` as a real number. -/
lemma cast_choose_two (k : ℕ) : ((k.choose 2 : ℕ) : ℝ) = (k : ℝ) * ((k : ℝ) - 1) / 2 := by
  rw [Nat.choose_two_right]
  rcases Nat.eq_zero_or_pos k with h | h
  · subst h; norm_num
  · have hdvd : (2 : ℕ) ∣ k * (k - 1) := even_iff_two_dvd.mp (Nat.even_mul_pred_self k)
    rw [Nat.cast_div hdvd (by norm_num : (2 : ℝ) ≠ 0)]
    push_cast [Nat.cast_sub (show 1 ≤ k by omega)]
    ring

/-! ## The ratio identities between the counting scalars -/

theorem cSq_eq_cDelta (m n : ℕ) : cSq m n = cDelta m n := by
  unfold cSq cDelta
  rw [card_Dsub m n, card_Dsub m m]

theorem cSq_mul (m n : ℕ) (hn : 3 ≤ n) (hnm : n ≤ m) :
    cSq m n * ((n : ℝ) - 2) = cAdj m n * ((m : ℝ) - 2) := by
  unfold cSq cAdj
  rw [card_Dsub m n, card_Dsub m m, card_Psub' m n hnm, card_Psub' m m le_rfl,
    card_Esub hnm, card_Esub le_rfl]
  simp only [Nat.cast_mul, Nat.cast_ofNat, Nat.cast_sub (show 2 ≤ n by omega),
    Nat.cast_sub (show 2 ≤ m by omega)]
  have h1 : (n.choose 2 : ℝ) ≠ 0 :=
    Nat.cast_ne_zero.mpr (Nat.choose_ne_zero (show 2 ≤ n by omega))
  have h2 : (m.choose 2 : ℝ) ≠ 0 :=
    Nat.cast_ne_zero.mpr (Nat.choose_ne_zero (show 2 ≤ m by omega))
  have h3 : ((n : ℝ) - 2) ≠ 0 := by
    have : (2 : ℝ) < n := by exact_mod_cast (by omega : 2 < n)
    linarith
  have h4 : ((m : ℝ) - 2) ≠ 0 := by
    have : (2 : ℝ) < m := by exact_mod_cast (by omega : 2 < m)
    linarith
  have h5 : ((2 : ℕ) : ℝ) ≠ 0 := by norm_num
  field_simp

theorem cOp_mul (m n : ℕ) (hm : 4 ≤ m) (hn : 4 ≤ n) (hnm : n ≤ m) :
    cOp m n * ((m:ℝ) - 3) = cAdj m n * ((n:ℝ) - 3) := by
  unfold cOp cAdj
  rw [card_Qsub' m n hnm, card_Qsub' m m le_rfl, card_Psub' m n hnm, card_Psub' m m le_rfl,
    card_Esub hnm, card_Esub le_rfl]
  push_cast [Nat.cast_sub (show 2 ≤ n by omega), Nat.cast_sub (show 2 ≤ m by omega)]
  rw [cast_choose_two (n - 2), cast_choose_two (m - 2)]
  push_cast [Nat.cast_sub (show 2 ≤ n by omega), Nat.cast_sub (show 2 ≤ m by omega)]
  have h1 : (n.choose 2 : ℝ) ≠ 0 :=
    Nat.cast_ne_zero.mpr (Nat.choose_ne_zero (show 2 ≤ n by omega))
  have h2 : (m.choose 2 : ℝ) ≠ 0 :=
    Nat.cast_ne_zero.mpr (Nat.choose_ne_zero (show 2 ≤ m by omega))
  have h3 : ((n : ℝ) - 2) ≠ 0 := by
    have : (2 : ℝ) < n := by exact_mod_cast (by omega : 2 < n)
    linarith
  have h4 : ((m : ℝ) - 2) ≠ 0 := by
    have : (2 : ℝ) < m := by exact_mod_cast (by omega : 2 < m)
    linarith
  have h5 : ((2 : ℕ) : ℝ) ≠ 0 := by norm_num
  have h6 : ((m : ℝ) - 3) ≠ 0 := by
    have : (3 : ℝ) < m := by exact_mod_cast (by omega : 3 < m)
    linarith
  have h7 : ((n : ℝ) - 3) ≠ 0 := by
    have : (3 : ℝ) < n := by exact_mod_cast (by omega : 3 < n)
    linarith
  have h8 : ((n : ℝ) - 2) * ((n : ℝ) - 3) ≠ 0 := mul_ne_zero h3 h7
  have h9 : ((m : ℝ) - 2) * ((m : ℝ) - 3) ≠ 0 := mul_ne_zero h4 h6
  have h10 : (6 - (m : ℝ) * 5 + (m : ℝ) ^ 2) ≠ 0 := by
    have hfac : 6 - (m : ℝ) * 5 + (m : ℝ) ^ 2 = ((m : ℝ) - 2) * ((m : ℝ) - 3) := by ring
    rw [hfac]; exact h9
  have h11 : (6 - (n : ℝ) * 5 + (n : ℝ) ^ 2) ≠ 0 := by
    have hfac : 6 - (n : ℝ) * 5 + (n : ℝ) ^ 2 = ((n : ℝ) - 2) * ((n : ℝ) - 3) := by ring
    rw [hfac]; exact h8
  have h12 : (-3 + (m : ℝ)) ≠ 0 := fun hh => h6 (by linarith)
  have h14 : ((m : ℝ) - 2 - 1) ≠ 0 := fun hh => h6 (by linarith)
  field_simp
  ring

lemma cAdj_pos (m n : ℕ) (hn : 3 ≤ n) (hnm : n ≤ m) : 0 < cAdj m n := by
  unfold cAdj
  have hPn : 0 < (Psub m n).card := by
    rw [card_Psub' m n hnm, card_Esub hnm]
    exact Nat.mul_pos (Nat.choose_pos (by omega)) (by omega)
  have hPm : 0 < (Psub m m).card := card_Psub_pos (by omega)
  positivity

lemma cSq_pos (m n : ℕ) (hn : 3 ≤ n) (hnm : n ≤ m) : 0 < cSq m n := by
  unfold cSq
  have hDn : 0 < (Dsub m n).card := by
    rw [card_Dsub, card_Esub hnm]
    exact Nat.choose_pos (by omega)
  have hDm : 0 < (Dsub m m).card := by
    rw [card_Dsub, card_Esub le_rfl]
    exact Nat.choose_pos (by omega)
  positivity

/-! ## The averaged certificate -/

/-- **The averaged certificate identity**: the `S_m`-average of the sub-simplex
certificate `Adj_n + k·Op_n − μ·Δ_n` is
`Adj_m + k(cOp/cAdj)·Op_m − (μ cSq/cAdj)·Δ_m`, up to the scalar `cAdj`. -/
theorem sum_permRingHom_cert (m n : ℕ) (hm : 4 ≤ m) (hn : 3 ≤ n) (k mu : ℝ) :
    (∑ σ : Equiv.Perm (Fin m),
        permRingHom σ (AdjPair m n + k • OpPair m n - mu • deltaSub m n))
      = cAdj m n • AdjLap m + (k * cOp m n) • OpLap m
          - (mu * cSq m n) • deltaSub m m := by
  classical
  have h1 : ∀ σ : Equiv.Perm (Fin m),
      permRingHom σ (AdjPair m n + k • OpPair m n - mu • deltaSub m n)
        = permRingHom σ (AdjPair m n) + k • permRingHom σ (OpPair m n)
            - mu • permRingHom σ (deltaSub m n) := by
    intro σ
    rw [map_sub, map_add, permRingHom_smul, permRingHom_smul]
  rw [Finset.sum_congr rfl (fun σ _ => h1 σ), Finset.sum_sub_distrib, Finset.sum_add_distrib,
    sum_smul_fintype k (fun σ : Equiv.Perm (Fin m) => permRingHom σ (OpPair m n)),
    sum_smul_fintype mu (fun σ : Equiv.Perm (Fin m) => permRingHom σ (deltaSub m n)),
    sum_permRingHom_AdjPair m n (by omega), sum_permRingHom_OpPair m n hm,
    sum_permRingHom_deltaSub m n (by omega)]
  rw [smul_smul, smul_smul, cSq_eq_cDelta m n]

/-! ## Method I -/

/-- **Kaluba–Kielak–Nowak, Method I.**  A certificate `Adj_n + k·Op_n − μ·Δ_n ∈ Σ²`
with `k·cOp ≤ cAdj` gives `Δ_m² − (μ cSq/cAdj)·Δ_m ∈ Σ²`. -/
theorem methodI (m n : ℕ) (hm : 4 ≤ m) (hn : 3 ≤ n) (hnm : n ≤ m) (k mu : ℝ) (hk : 0 ≤ k)
    (hcond : k * cOp m n ≤ cAdj m n)
    (hcert : IsSOS (AdjPair m n + k • OpPair m n - mu • deltaSub m n)) :
    IsSOS (deltaSub m m ^ 2 - (mu * (cSq m n / cAdj m n)) • deltaSub m m) := by
  classical
  have ht : 0 < cAdj m n := cAdj_pos m n hn hnm
  have htne : cAdj m n ≠ 0 := ne_of_gt ht
  -- the averaged certificate is a sum of hermitian squares
  have hZ : IsSOS (∑ σ : Equiv.Perm (Fin m),
      permRingHom σ (AdjPair m n + k • OpPair m n - mu • deltaSub m n)) := by
    refine IsSOS.finset_sum Finset.univ (fun σ _ => ?_)
    exact IsSOS.map (permRingHom σ) (permRingHom_star σ) hcert
  have hZid := sum_permRingHom_cert m n hm hn k mu
  have hscal : cAdj m n * (mu * (cSq m n / cAdj m n)) = mu * cSq m n := by
    field_simp
  have hmain : cAdj m n • (deltaSub m m ^ 2 - (mu * (cSq m n / cAdj m n)) • deltaSub m m)
      = cAdj m n • SqLap m + (cAdj m n - k * cOp m n) • OpLap m
          + (∑ σ : Equiv.Perm (Fin m),
              permRingHom σ (AdjPair m n + k • OpPair m n - mu • deltaSub m n)) := by
    rw [hZid, deltaSub_sq_eq, smul_sub, smul_add, smul_add, smul_smul, hscal]
    module
  have hSOS : IsSOS (cAdj m n • (deltaSub m m ^ 2 - (mu * (cSq m n / cAdj m n)) • deltaSub m m)) := by
    rw [hmain]
    exact ((IsSOS.smul (le_of_lt ht) (isSOS_SqLap m)).add
      (IsSOS.smul (sub_nonneg.mpr hcond) (isSOS_OpLap m))).add hZ
  have hsplit : deltaSub m m ^ 2 - (mu * (cSq m n / cAdj m n)) • deltaSub m m
      = (cAdj m n)⁻¹ • (cAdj m n •
          (deltaSub m m ^ 2 - (mu * (cSq m n / cAdj m n)) • deltaSub m m)) := by
    rw [smul_smul, inv_mul_cancel₀ htne, one_smul]
  rw [hsplit]
  exact IsSOS.smul (le_of_lt (inv_pos.mpr ht)) hSOS

/-- **Method I in the form used for the applications.**  A certificate
`Adj_n + k·Op_n − μ·Δ_n ∈ Σ²` with `k·(n−3) ≤ m−3` gives
`Δ_m² − (μ(m−2)/(n−2))·Δ_m ∈ Σ²`. -/
theorem methodI' (m n : ℕ) (hm : 4 ≤ m) (hn : 4 ≤ n) (hnm : n ≤ m) (k mu : ℝ) (hk : 0 ≤ k)
    (hcond : k * ((n : ℝ) - 3) ≤ (m : ℝ) - 3)
    (hcert : IsSOS (AdjPair m n + k • OpPair m n - mu • deltaSub m n)) :
    IsSOS (deltaSub m m ^ 2 - (mu * (((m : ℝ) - 2) / ((n : ℝ) - 2))) • deltaSub m m) := by
  have hkey : k * cOp m n ≤ cAdj m n := by
    have hcop := cOp_mul m n hm (by omega) hnm
    have hm3 : (0 : ℝ) < (m : ℝ) - 3 := by
      have : (3 : ℝ) < m := by exact_mod_cast (by omega : 3 < m)
      linarith
    have hc : (0 : ℝ) ≤ cAdj m n := le_of_lt (cAdj_pos m n (by omega) hnm)
    have h1 : k * cOp m n * ((m : ℝ) - 3) ≤ cAdj m n * ((m : ℝ) - 3) := by
      calc k * cOp m n * ((m : ℝ) - 3)
          = k * (cOp m n * ((m : ℝ) - 3)) := by ring
        _ = k * (cAdj m n * ((n : ℝ) - 3)) := by rw [hcop]
        _ = (k * ((n : ℝ) - 3)) * cAdj m n := by ring
        _ ≤ ((m : ℝ) - 3) * cAdj m n := mul_le_mul_of_nonneg_right hcond hc
        _ = cAdj m n * ((m : ℝ) - 3) := by ring
    exact le_of_mul_le_mul_right h1 hm3
  have hn2 : (0 : ℝ) < (n : ℝ) - 2 := by
    have : (2 : ℝ) < n := by exact_mod_cast (by omega : 2 < n)
    linarith
  have hratio : cSq m n / cAdj m n = ((m : ℝ) - 2) / ((n : ℝ) - 2) := by
    rw [div_eq_div_iff (ne_of_gt (cAdj_pos m n (by omega) hnm)) (ne_of_gt hn2)]
    rw [cSq_mul m n (by omega) hnm]
    ring
  have h := methodI m n hm (by omega) hnm k mu hk hkey hcert
  rwa [hratio] at h

/-- **Method I gives property (T) for `Aut(F_m)`** (via the index-two ascent of
`Submission.Nielsen.propertyT_aut_of_sAutGen_certificate''`). -/
theorem propertyT_aut_of_methodI (m n : ℕ) (hm : 6 ≤ m) (hn : 4 ≤ n) (hnm : n ≤ m)
    (k mu : ℝ) (hk : 0 ≤ k) (hmu : 0 < mu) (hcond : k * ((n : ℝ) - 3) ≤ (m : ℝ) - 3)
    (hcert : IsSOS (AdjPair m n + k • OpPair m n - mu • deltaSub m n)) :
    PropertyT (MulAut (FreeGroup (Fin m))) := by
  have hcert' := methodI' m n (by omega) hn hnm k mu hk hcond hcert
  obtain ⟨ξ, hξ⟩ := hcert'
  have hpos : 0 < mu * (((m : ℝ) - 2) / ((n : ℝ) - 2)) := by
    have : (0 : ℝ) < (m : ℝ) - 2 := by
      have : (2 : ℝ) < m := by exact_mod_cast (by omega : 2 < m)
      linarith
    have : (0 : ℝ) < (n : ℝ) - 2 := by
      have : (2 : ℝ) < n := by exact_mod_cast (by omega : 2 < n)
      linarith
    positivity
  refine Submission.Nielsen.propertyT_aut_of_sAutGen_certificate'' m ⟨0, by omega⟩
    (mu * (((m : ℝ) - 2) / ((n : ℝ) - 2))) hpos ξ ?_
  rw [← deltaSub_top]
  exact hξ

end Edge

end Submission.RouteB
