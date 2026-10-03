/-
# The gluing of the two branches of `Work.KMTAreas.A4Z.lipTwoGenTail`

`Work.KMTAreas.A4Z.LipOutputGenTwoTail P ρ A C K C0 K2` is proved by splitting on
`N^d ≤ C δ^{-K}`:

* the **small-`N`** branch (`A4Z/smallTail.lean`) truncates the second dual function to the window
  `[-⌊A N^d⌋, ⌊A N^d⌋]`; its Fourier support lives in the vacuous `majorArc ρ 0 0 = Set.univ`, and
  the truncation makes the `ℓ¹`-fringe clause hold with equality.  It is formalised here as
  `SmallTailBranch P`, the parametric form `Work.KMTAreas.A4Z.smallTailK`;
* the **large-`N`** branch is the paper's §5.2 chain; in its *unscaled* form it produces `G` with
  `‖G‖_∞ ≤ 1`, `∑‖G‖ ≤ 1 + N^d`, Fourier support in `majorArc ρ l k` with
  `2^l ≤ δ^{-(c+1)}`, `2^k ≤ δ^{-(c+1)}/N^d`, correlation `D δ^c N^d ≤ |⟨g,G⟩|`, the `ℓ¹`-fringe
  `∑_{|x|>AN^d}‖G x‖ ≤ Dδ^cN^d/2` and the `ℓ²`-tail `∑_{|x|>RN^d}‖G x‖² ≤ C₂²R^{-1}N^d`.  It is
  formalised here as `LargeTailBranch P`.

The gluing chooses `K := max 1 (c+1) (K_big·d)` (so that the complement of the small case
`N^d > Cδ^{-K}` implies the large case's hypothesis `C_big δ^{-K_big} ≤ N`, and so that the
rescaling `λ := δ^{K-c}/D` normalises the correlation to `δ^K N^d`), and rescales the large
branch's output by `λ`.  Every clause is preserved by this rescaling, the two tail clauses because
the large branch states the `ℓ¹`-fringe *relative* to its own correlation (`≤ Dδ^cN^d/2`) and the
`ℓ²`-tail with the *same* exponent `1` as the target.
-/
import Mathlib
import Submission.Work.KMTAreas.A4Z.Defs
import Submission.Work.KMTAreas.A4.lip2Step1

set_option autoImplicit false
set_option maxHeartbeats 2000000

open scoped BigOperators
open Polynomial
open Work.Analysis.InverseTheory

namespace Work.KMTAreas.A4Z

/-- **The small-`N` branch** in the form needed by the gluing: for prescribed `K, C₀, K₂` there is
a threshold `Cmin` such that for *every* `C ≥ Cmin` the branch holds with the constant `C`
(this is the parametric form of `Work.KMTAreas.A4Z.smallTailK`, whose construction — the second
dual function truncated to the window — does not depend on `C`). -/
def SmallTailBranch (P : Polynomial ℤ) : Prop :=
  ∀ (A : ℝ), 1 ≤ A → ∀ (K C0 K2 : ℝ), 1 ≤ K → 1 ≤ C0 → 1 ≤ K2 → A ^ (K2 - 1) ≤ C0 ^ 2 →
    ∃ Cmin : ℝ, 1 ≤ Cmin ∧ ∀ (C : ℝ), Cmin ≤ C → ∀ (ρ : ℝ), 0 < ρ → ρ ≤ 1 →
      ∀ (N N₀ : ℕ) (δ : ℝ) (f g h : ℤ → ℂ), 1 ≤ N → 0 < δ → δ ≤ 1 →
        A * (N : ℝ) ^ P.natDegree / 2 ≤ (N₀ : ℝ) → (N₀ : ℝ) ≤ A * (N : ℝ) ^ P.natDegree →
        SupportIn f N₀ → SupportIn g N₀ → SupportIn h N₀ →
        (∀ x : ℤ, ‖f x‖ ≤ 1) → (∀ x : ℤ, ‖g x‖ ≤ 1) → (∀ x : ℤ, ‖h x‖ ≤ 1) →
        δ * (N : ℝ) ^ P.natDegree ≤ ‖bilinPair (AhalfZ N P f g) h‖ →
        (N : ℝ) ^ P.natDegree ≤ C * δ⁻¹ ^ K →
        ∃ (G : ℤ → ℂ) (l : ℕ) (k : ℤ),
          (∀ x : ℤ, ‖G x‖ ≤ C * A * δ⁻¹ ^ K) ∧
          Summable (fun x : ℤ => ‖G x‖) ∧
          (∑' x : ℤ, ‖G x‖ ≤ C * A * δ⁻¹ ^ K * (N : ℝ) ^ P.natDegree) ∧
          FourierSupportIn G (majorArc ρ l k) ∧
          (2 : ℝ) ^ l ≤ C * A * δ⁻¹ ^ K ∧
          (2 : ℝ) ^ k ≤ C * A * δ⁻¹ ^ K / (N : ℝ) ^ P.natDegree ∧
          δ ^ K * (N : ℝ) ^ P.natDegree ≤ ‖bilinPair g G‖ ∧
          (∑' x : ℤ, (if A * (N : ℝ) ^ P.natDegree < |(x : ℝ)| then ‖G x‖ else 0)
            ≤ δ ^ K * (N : ℝ) ^ P.natDegree / 2) ∧
          (∀ R : ℝ, 1 ≤ R →
            ∑' x : ℤ, (if R * (N : ℝ) ^ P.natDegree < |(x : ℝ)| then ‖G x‖ ^ 2 else 0)
              ≤ C0 ^ 2 * R ^ (-(K2)) * (C * A * δ⁻¹ ^ K) ^ 2 * (N : ℝ) ^ P.natDegree)

/-- **The large-`N` branch** in the unscaled form delivered by the §5.2 chain (the output of
`Work.KMTAreas.A4Z.largeTail`). -/
def LargeTailBranch (P : Polynomial ℤ) : Prop :=
  ∀ (A : ℝ), 1 ≤ A →
    ∃ (c D Kbig Cbig Cl Ck C2 : ℝ), 0 < c ∧ 0 < D ∧ 0 < Kbig ∧ 0 < Cbig ∧ 0 < Cl ∧ 0 < Ck ∧ 0 < C2 ∧
      ∀ (ρ : ℝ), 0 < ρ → ρ ≤ 1 →
      ∀ (N N₀ : ℕ) (δ : ℝ) (f g h : ℤ → ℂ), 1 ≤ N → 0 < δ → δ ≤ 1 →
        A * (N : ℝ) ^ P.natDegree / 2 ≤ (N₀ : ℝ) → (N₀ : ℝ) ≤ A * (N : ℝ) ^ P.natDegree →
        SupportIn f N₀ → SupportIn g N₀ → SupportIn h N₀ →
        (∀ x : ℤ, ‖f x‖ ≤ 1) → (∀ x : ℤ, ‖g x‖ ≤ 1) → (∀ x : ℤ, ‖h x‖ ≤ 1) →
        δ * (N : ℝ) ^ P.natDegree ≤ ‖bilinPair (AhalfZ N P f g) h‖ →
        Cbig * δ⁻¹ ^ Kbig ≤ (N : ℝ) →
        ∃ (G : ℤ → ℂ) (l : ℕ) (k : ℤ),
          (∀ x : ℤ, ‖G x‖ ≤ 1) ∧ Summable (fun x : ℤ => ‖G x‖) ∧
          (∑' x : ℤ, ‖G x‖ ≤ 1 + (N : ℝ) ^ P.natDegree) ∧
          FourierSupportIn G (majorArc ρ l k) ∧
          (2 : ℝ) ^ l ≤ Cl * δ⁻¹ ^ (c + 1) ∧
          (2 : ℝ) ^ k ≤ Ck * δ⁻¹ ^ (c + 1) / (N : ℝ) ^ P.natDegree ∧
          D * δ ^ c * (N : ℝ) ^ P.natDegree ≤ ‖bilinPair g G‖ ∧
          (∑' x : ℤ, (if A * (N : ℝ) ^ P.natDegree < |(x : ℝ)| then ‖G x‖ else 0)
            ≤ D * δ ^ c * (N : ℝ) ^ P.natDegree / 2) ∧
          (∀ R : ℝ, 1 ≤ R →
            ∑' x : ℤ, (if R * (N : ℝ) ^ P.natDegree < |(x : ℝ)| then ‖G x‖ ^ 2 else 0)
              ≤ C2 ^ 2 * R ^ (-(1 : ℝ)) * (N : ℝ) ^ P.natDegree)

theorem glue (P : Polynomial ℤ) (hP : 2 ≤ P.natDegree)
    (hsmall : SmallTailBranch P) (hlarge : LargeTailBranch P) :
    ∀ (A : ℝ), 1 ≤ A → ∃ C K C0 K2 : ℝ,
      0 < C ∧ 0 < K ∧ 0 < C0 ∧ 0 < K2 ∧
      ∀ (ρ : ℝ), 0 < ρ → ρ ≤ 1 → LipOutputGenTwoTail P ρ A C K C0 K2 := by
  intro A hA
  obtain ⟨c, D, Kbig, Cbig, Cl, Ck, C2, hc0, hD0, hKbig0, hCbig0, hCl0, hCk0, hC20, hL⟩ := hlarge A hA
  have hA0 : (0 : ℝ) < A := lt_of_lt_of_le zero_lt_one hA
  have hA1 : (1 : ℝ) ≤ A := hA
  -- the final K2 = C0
  set K2 : ℝ := 1 with hK2def
  have hK2_1 : 1 ≤ K2 := by rw [hK2def]
  have hK2pos : 0 < K2 := lt_of_lt_of_le zero_lt_one hK2_1
  set C0 : ℝ := max 1 C2 with hC0def
  have hC0_1 : 1 ≤ C0 := le_max_left 1 C2
  have hC0pos : 0 < C0 := lt_of_lt_of_le zero_lt_one hC0_1
  have hC2_le : C2 ≤ C0 := le_max_right 1 C2
  have hAexp : A ^ (K2 - 1) ≤ C0 ^ 2 := by
    have h1 : A ^ (K2 - 1) = 1 := by rw [hK2def]; norm_num
    rw [h1]; nlinarith [hC0_1]
  -- the final K
  set K : ℝ := max 1 (max (c + 1) (Kbig * (P.natDegree : ℝ))) with hKdef
  have hK_1 : 1 ≤ K := le_max_left 1 _
  have hKpos : 0 < K := lt_of_lt_of_le zero_lt_one hK_1
  have hK_c1 : c + 1 ≤ K := le_trans (le_max_left (c + 1) _) (le_max_right 1 _)
  have hK_Kbig : Kbig * (P.natDegree : ℝ) ≤ K :=
    le_trans (le_max_right (c + 1) _) (le_max_right 1 _)
  obtain ⟨Cs, hCspos, hS⟩ := hsmall A hA K C0 K2 hK_1 hC0_1 hK2_1 hAexp
  -- the final C
  set C : ℝ := max Cs (max (Cbig ^ P.natDegree)
    (max (2 / D + 1) (max (C2 / D) (max (Cl / A) (Ck / A))))) with hCdef
  have hC_Cs : Cs ≤ C := by rw [hCdef]; exact le_max_left _ _
  have hC_Kbig : Cbig ^ P.natDegree ≤ C := by
    rw [hCdef]
    exact le_trans (le_max_left (Cbig ^ P.natDegree)
      (max (2 / D + 1) (max (C2 / D) (max (Cl / A) (Ck / A))))) (le_max_right Cs _)
  have hC_D : 2 / D + 1 ≤ C := by
    rw [hCdef]
    exact le_trans (le_trans (le_max_left (2 / D + 1) (max (C2 / D) (max (Cl / A) (Ck / A))))
      (le_max_right (Cbig ^ P.natDegree) _)) (le_max_right Cs _)
  have hC_C2 : C2 / D ≤ C := by
    rw [hCdef]
    exact le_trans (le_trans (le_trans (le_max_left (C2 / D) (max (Cl / A) (Ck / A)))
      (le_max_right (2 / D + 1) _)) (le_max_right (Cbig ^ P.natDegree) _)) (le_max_right Cs _)
  have hC_Cl : Cl / A ≤ C := by
    rw [hCdef]
    exact le_trans (le_trans (le_trans (le_max_left (Cl / A) (Ck / A))
      (le_max_right (C2 / D) _)) (le_max_right (2 / D + 1) _))
      (le_trans (le_max_right (Cbig ^ P.natDegree) _) (le_max_right Cs _))
  have hC_Ck : Ck / A ≤ C := by
    rw [hCdef]
    exact le_trans (le_trans (le_trans (le_max_right (Cl / A) (Ck / A))
      (le_max_right (C2 / D) _)) (le_max_right (2 / D + 1) _))
      (le_trans (le_max_right (Cbig ^ P.natDegree) _) (le_max_right Cs _))
  have hC_1 : 1 ≤ C := by
    refine le_trans ?_ hC_D
    have h1 : (0 : ℝ) ≤ 2 / D := div_nonneg (by norm_num) hD0.le
    linarith
  have hCpos : 0 < C := lt_of_lt_of_le zero_lt_one hC_1
  have hCAD : 2 ≤ C * A * D := by
    have h2 : (0 : ℝ) ≤ A * D := mul_nonneg hA0.le hD0.le
    have h3 : 2 / D + 1 ≤ C := hC_D
    have h5 : (2 / D + 1) * D = 2 + D := by field_simp
    have h6 : (2 / D + 1) * A * D = ((2 / D + 1) * D) * A := by ring
    have h4 : 2 ≤ (2 / D + 1) * A * D := by
      rw [h6, h5]
      nlinarith [hA1, hD0]
    have h1 : (2 / D + 1) * A * D ≤ C * A * D := by nlinarith [h2, h3]
    linarith [h1, h4]
  refine ⟨C, K, C0, K2, hCpos, hKpos, hC0pos, hK2pos, ?_⟩
  intro ρ hρ0 hρ1
  intro N N₀ δ f g h hN hδ0 hδ1 hN0lo hN0hi hfs hgs hhs hfb hgb hhb hcorr
  have hδinv0 : (0 : ℝ) ≤ δ⁻¹ := inv_nonneg.mpr hδ0.le
  have hδinv1 : (1 : ℝ) ≤ δ⁻¹ := (one_le_inv₀ hδ0).mpr hδ1
  have hNdpos : (0 : ℝ) < (N : ℝ) ^ P.natDegree := by
    have : (0 : ℝ) < (N : ℝ) := by exact_mod_cast hN
    positivity
  have hNd1 : (1 : ℝ) ≤ (N : ℝ) ^ P.natDegree := one_le_pow₀ (by exact_mod_cast hN)
  by_cases hcase : (N : ℝ) ^ P.natDegree ≤ C * δ⁻¹ ^ K
  · -- ## the small-`N` branch: apply the parametric branch at the merged constant `C ≥ Cmin`
    exact hS C hC_Cs ρ hρ0 hρ1 N N₀ δ f g h hN hδ0 hδ1 hN0lo hN0hi hfs hgs hhs hfb hgb hhb
      hcorr hcase
  · -- ## the large-`N` branch
    have hlt : C * δ⁻¹ ^ K < (N : ℝ) ^ P.natDegree := lt_of_not_ge hcase
    have hNpos : (0 : ℝ) < (N : ℝ) := by exact_mod_cast hN
    have hd1 : (0 : ℝ) < (P.natDegree : ℝ) := by
      exact_mod_cast (by omega : 0 < P.natDegree)
    -- the large case's hypothesis, from the complement of the small case
    have hCle : Cbig ≤ C ^ ((P.natDegree : ℝ))⁻¹ := by
      have h6 : (Cbig ^ P.natDegree) ^ ((P.natDegree : ℝ))⁻¹ = Cbig := by
        rw [← Real.rpow_natCast Cbig P.natDegree, ← Real.rpow_mul hCbig0.le,
          mul_inv_cancel₀ (ne_of_gt hd1), Real.rpow_one]
      calc Cbig = (Cbig ^ P.natDegree) ^ ((P.natDegree : ℝ))⁻¹ := h6.symm
        _ ≤ C ^ ((P.natDegree : ℝ))⁻¹ := Real.rpow_le_rpow (by positivity) hC_Kbig (by positivity)
    have hδle : δ⁻¹ ^ Kbig ≤ δ⁻¹ ^ (K * ((P.natDegree : ℝ))⁻¹) := by
      refine Real.rpow_le_rpow_of_exponent_le ((one_le_inv₀ hδ0).mpr hδ1) ?_
      have hk : Kbig * (P.natDegree : ℝ) * ((P.natDegree : ℝ))⁻¹
          ≤ K * ((P.natDegree : ℝ))⁻¹ :=
        mul_le_mul_of_nonneg_right hK_Kbig (by positivity)
      rwa [mul_assoc, mul_inv_cancel₀ (ne_of_gt hd1), mul_one] at hk
    have hstep1 : (C * δ⁻¹ ^ K) ^ ((P.natDegree : ℝ))⁻¹ ≤ (N : ℝ) := by
      have h := Real.rpow_le_rpow (le_of_lt (mul_pos hCpos (Real.rpow_pos_of_pos (inv_pos.mpr hδ0) K)))
        (le_of_lt hlt) (by positivity : (0 : ℝ) ≤ ((P.natDegree : ℝ))⁻¹)
      have h2 : ((N : ℝ) ^ P.natDegree) ^ ((P.natDegree : ℝ))⁻¹ = (N : ℝ) := by
        rw [← Real.rpow_natCast (N : ℝ) P.natDegree, ← Real.rpow_mul (le_of_lt hNpos),
          mul_inv_cancel₀ (ne_of_gt hd1), Real.rpow_one]
      rwa [h2] at h
    have hsplit : (C * δ⁻¹ ^ K) ^ ((P.natDegree : ℝ))⁻¹
        = C ^ ((P.natDegree : ℝ))⁻¹ * δ⁻¹ ^ (K * ((P.natDegree : ℝ))⁻¹) := by
      rw [Real.mul_rpow hCpos.le (Real.rpow_pos_of_pos (inv_pos.mpr hδ0) K).le,
        ← Real.rpow_mul hδinv0 K ((P.natDegree : ℝ))⁻¹]
    have hbig : Cbig * δ⁻¹ ^ Kbig ≤ (N : ℝ) :=
      calc Cbig * δ⁻¹ ^ Kbig
          ≤ C ^ ((P.natDegree : ℝ))⁻¹ * δ⁻¹ ^ (K * ((P.natDegree : ℝ))⁻¹) :=
            mul_le_mul hCle hδle (Real.rpow_nonneg hδinv0 Kbig) (by positivity)
        _ = (C * δ⁻¹ ^ K) ^ ((P.natDegree : ℝ))⁻¹ := hsplit.symm
        _ ≤ (N : ℝ) := hstep1
    obtain ⟨G0, l, k, h1, h2, h3, h4, h5, h6, h7, h8, h9⟩ :=
      hL ρ hρ0 hρ1 N N₀ δ f g h hN hδ0 hδ1 hN0lo hN0hi hfs hgs hhs hfb hgb hhb hcorr hbig
    -- the rescaling
    set lam : ℝ := δ ^ (K - c) / D with hlamdef
    have hlampos : 0 < lam := div_pos (Real.rpow_pos_of_pos hδ0 _) hD0
    have hlamnorm : ‖((lam : ℝ) : ℂ)‖ = lam := by
      rw [Complex.norm_real, Real.norm_of_nonneg hlampos.le]
    have hlamD : lam * (D * δ ^ c) = δ ^ K := by
      rw [hlamdef]
      field_simp
      rw [← Real.rpow_add hδ0 (K - c) c]
      congr 1
      ring
    have hδKpos : 0 < δ ^ K := Real.rpow_pos_of_pos hδ0 K
    have hlam_le : 2 * lam ≤ C * A * δ⁻¹ ^ K := by
      have hexp : (0 : ℝ) ≤ 2 * K - c := by linarith [hK_c1]
      have hδ2 : δ ^ (2 * K - c) ≤ 1 := Real.rpow_le_one hδ0.le hδ1 hexp
      have h3 : 2 * δ ^ (2 * K - c) ≤ C * A * D := by linarith [hδ2, hCAD]
      have hexp2 : δ ^ (K - c) = δ ^ (2 * K - c) * (δ ^ K)⁻¹ := by
        rw [← Real.rpow_neg hδ0.le K, ← Real.rpow_add hδ0]
        congr 1
        ring
      -- `2 * lam * δ^K = 2 * δ^(2K-c) / D`
      have h1 : 2 * lam * δ ^ K = (2 * δ ^ (2 * K - c)) / D := by
        rw [hlamdef, hexp2]
        field_simp
      have h2 : C * A = (C * A * D) / D := by
        field_simp
      have hstep : 2 * lam * δ ^ K ≤ C * A := by
        rw [h1, h2]
        exact div_le_div_of_nonneg_right h3 hD0.le
      calc 2 * lam = (2 * lam * δ ^ K) * (δ ^ K)⁻¹ := by
            rw [mul_assoc, mul_inv_cancel₀ hδKpos.ne', mul_one]
        _ ≤ (C * A) * (δ ^ K)⁻¹ := mul_le_mul_of_nonneg_right hstep (by positivity)
        _ = C * A * δ⁻¹ ^ K := by rw [← Real.inv_rpow hδ0.le K]
    refine ⟨fun x => ((lam : ℝ) : ℂ) * G0 x, l, k, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · intro x
      calc ‖((lam : ℝ) : ℂ) * G0 x‖ = lam * ‖G0 x‖ := by rw [norm_mul, hlamnorm]
        _ ≤ lam * 1 := mul_le_mul_of_nonneg_left (h1 x) hlampos.le
        _ = lam := mul_one lam
        _ ≤ 2 * lam := by linarith [hlampos.le]
        _ ≤ C * A * δ⁻¹ ^ K := hlam_le
    · exact (h2.mul_left lam).congr fun x => by rw [norm_mul, hlamnorm]
    · have hsum : (∑' x : ℤ, ‖((lam : ℝ) : ℂ) * G0 x‖) = lam * ∑' x : ℤ, ‖G0 x‖ := by
        rw [← tsum_mul_left]
        exact tsum_congr fun x => by rw [norm_mul, hlamnorm]
      rw [hsum]
      calc lam * (∑' x : ℤ, ‖G0 x‖) ≤ lam * (1 + (N : ℝ) ^ P.natDegree) :=
            mul_le_mul_of_nonneg_left h3 hlampos.le
        _ ≤ lam * (2 * (N : ℝ) ^ P.natDegree) := by
            refine mul_le_mul_of_nonneg_left ?_ hlampos.le
            linarith [hNd1]
        _ = (2 * lam) * (N : ℝ) ^ P.natDegree := by ring
        _ ≤ C * A * δ⁻¹ ^ K * (N : ℝ) ^ P.natDegree := by
            refine mul_le_mul_of_nonneg_right hlam_le hNdpos.le
    · exact Work.KMTAreas.A4.FourierSupportIn_const_mul h2 ((lam : ℝ) : ℂ) h4
    · refine h5.trans ?_
      have h1 : δ⁻¹ ^ (c + 1) ≤ δ⁻¹ ^ K :=
        Real.rpow_le_rpow_of_exponent_le hδinv1 hK_c1
      have hClCA : Cl ≤ C * A := by
        have h := hC_Cl
        rw [div_le_iff₀ hA0] at h
        exact h
      calc Cl * δ⁻¹ ^ (c + 1) ≤ Cl * δ⁻¹ ^ K := mul_le_mul_of_nonneg_left h1 hCl0.le
        _ ≤ C * A * δ⁻¹ ^ K := mul_le_mul_of_nonneg_right hClCA (Real.rpow_nonneg hδinv0 K)
    · refine h6.trans ?_
      have h1 : δ⁻¹ ^ (c + 1) ≤ δ⁻¹ ^ K :=
        Real.rpow_le_rpow_of_exponent_le hδinv1 hK_c1
      have hCkCA : Ck ≤ C * A := by
        have h := hC_Ck
        rw [div_le_iff₀ hA0] at h
        exact h
      have hstep : Ck * δ⁻¹ ^ (c + 1) ≤ C * A * δ⁻¹ ^ K :=
        calc Ck * δ⁻¹ ^ (c + 1) ≤ Ck * δ⁻¹ ^ K := mul_le_mul_of_nonneg_left h1 hCk0.le
          _ ≤ C * A * δ⁻¹ ^ K := mul_le_mul_of_nonneg_right hCkCA (Real.rpow_nonneg hδinv0 K)
      exact div_le_div_of_nonneg_right hstep hNdpos.le
    · have hsmul : bilinPair g (fun x => ((lam : ℝ) : ℂ) * G0 x)
          = ((lam : ℝ) : ℂ) * bilinPair g G0 := by
        rw [bilinPair, bilinPair, ← tsum_mul_left]
        exact tsum_congr fun x => by ring
      rw [hsmul, norm_mul, hlamnorm]
      calc δ ^ K * (N : ℝ) ^ P.natDegree
          = lam * (D * δ ^ c * (N : ℝ) ^ P.natDegree) := by
            rw [← hlamD]; ring
        _ ≤ lam * ‖bilinPair g G0‖ := mul_le_mul_of_nonneg_left h7 hlampos.le
    · have htail : (∑' x : ℤ, (if A * (N : ℝ) ^ P.natDegree < |(x : ℝ)| then
            ‖((lam : ℝ) : ℂ) * G0 x‖ else 0))
          = lam * ∑' x : ℤ, (if A * (N : ℝ) ^ P.natDegree < |(x : ℝ)| then ‖G0 x‖ else 0) := by
        rw [← tsum_mul_left]
        exact tsum_congr fun x => by
          by_cases hx : A * (N : ℝ) ^ P.natDegree < |(x : ℝ)|
          · rw [if_pos hx, if_pos hx, norm_mul, hlamnorm]
          · rw [if_neg hx, if_neg hx, mul_zero]
      rw [htail]
      calc lam * (∑' x : ℤ, (if A * (N : ℝ) ^ P.natDegree < |(x : ℝ)| then ‖G0 x‖ else 0))
          ≤ lam * (D * δ ^ c * (N : ℝ) ^ P.natDegree / 2) :=
            mul_le_mul_of_nonneg_left h8 hlampos.le
        _ = δ ^ K * (N : ℝ) ^ P.natDegree / 2 := by
            rw [← hlamD]; ring
    · intro R hR
      have htail : (∑' x : ℤ, (if R * (N : ℝ) ^ P.natDegree < |(x : ℝ)| then
            ‖((lam : ℝ) : ℂ) * G0 x‖ ^ 2 else 0))
          = lam ^ 2 * ∑' x : ℤ, (if R * (N : ℝ) ^ P.natDegree < |(x : ℝ)| then ‖G0 x‖ ^ 2 else 0) := by
        rw [show (fun x : ℤ => (if R * (N : ℝ) ^ P.natDegree < |(x : ℝ)| then
            ‖((lam : ℝ) : ℂ) * G0 x‖ ^ 2 else 0))
          = fun x : ℤ => lam ^ 2 * (if R * (N : ℝ) ^ P.natDegree < |(x : ℝ)| then
              ‖G0 x‖ ^ 2 else 0) from funext fun x => by
            by_cases hx : R * (N : ℝ) ^ P.natDegree < |(x : ℝ)|
            · rw [if_pos hx, if_pos hx, norm_mul, hlamnorm]; ring
            · rw [if_neg hx, if_neg hx, mul_zero]]
        rw [tsum_mul_left]
      rw [htail]
      have h9' := h9 R hR
      have hRpow : R ^ (-(1 : ℝ)) = R⁻¹ := Real.rpow_neg_one R
      rw [hRpow] at h9'
      have hgoal : lam ^ 2 * (C2 ^ 2 * R⁻¹ * (N : ℝ) ^ P.natDegree)
          ≤ C0 ^ 2 * R ^ (-(K2)) * (C * A * δ⁻¹ ^ K) ^ 2 * (N : ℝ) ^ P.natDegree := by
        rw [hK2def, Real.rpow_neg_one]
        have hRpos : (0 : ℝ) < R := lt_of_lt_of_le zero_lt_one hR
        have hlam2 : lam ^ 2 ≤ (C * A * δ⁻¹ ^ K) ^ 2 := by
          have h1 : (0 : ℝ) ≤ lam := hlampos.le
          have h2 : (0 : ℝ) ≤ C * A * δ⁻¹ ^ K :=
            mul_nonneg (mul_nonneg hCpos.le hA0.le) (Real.rpow_nonneg hδinv0 K)
          have h3 : lam ≤ C * A * δ⁻¹ ^ K := by linarith [hlam_le, h1]
          nlinarith [h3, h1, h2]
        have hC2sq : C2 ^ 2 ≤ C0 ^ 2 := by
          have h1 : (0 : ℝ) ≤ C2 := hC20.le
          nlinarith [hC2_le, h1]
        have h1 : lam ^ 2 * (C2 ^ 2 * R⁻¹ * (N : ℝ) ^ P.natDegree)
            = (lam ^ 2 * C2 ^ 2) * R⁻¹ * (N : ℝ) ^ P.natDegree := by ring
        have h2 : (C * A * δ⁻¹ ^ K) ^ 2 * C0 ^ 2 * R⁻¹ * (N : ℝ) ^ P.natDegree
            = C0 ^ 2 * R⁻¹ * (C * A * δ⁻¹ ^ K) ^ 2 * (N : ℝ) ^ P.natDegree := by ring
        rw [h1, ← h2]
        have hnn : (0 : ℝ) ≤ R⁻¹ := inv_nonneg.mpr hRpos.le
        have hprod : lam ^ 2 * C2 ^ 2 ≤ (C * A * δ⁻¹ ^ K) ^ 2 * C0 ^ 2 := by nlinarith [hlam2, hC2sq]
        have hNn : (0 : ℝ) ≤ (N : ℝ) ^ P.natDegree := hNdpos.le
        calc (lam ^ 2 * C2 ^ 2) * R⁻¹ * (N : ℝ) ^ P.natDegree
            ≤ ((C * A * δ⁻¹ ^ K) ^ 2 * C0 ^ 2) * R⁻¹ * (N : ℝ) ^ P.natDegree := by gcongr
          _ = (C * A * δ⁻¹ ^ K) ^ 2 * C0 ^ 2 * R⁻¹ * (N : ℝ) ^ P.natDegree := by ring
      exact (mul_le_mul_of_nonneg_left h9' (sq_nonneg lam)).trans hgoal

end Work.KMTAreas.A4Z
