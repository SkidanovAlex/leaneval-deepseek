import Mathlib
import Submission.Work.Diff.Alg.Pinch.Defs
import Submission.Work.Diff.Alg.Pinch.Strict
import Submission.Work.Diff.Alg.Pinch.Delta
import Submission.Work.Diff.Alg.Pinch.ric_knProd_id2
import Submission.Work.Diff.Alg.Pinch.scalAlg_knProd
import Submission.Work.Diff.Alg.Pinch.ell_inv
import Submission.Work.Diff.Alg.Pinch.ell_isAlgCurv
import Submission.Work.Diff.Alg.Pinch.inPIC2_cone_basic

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

/-!
# Auxiliary algebra for `Ccone_transversal_a`

Bookkeeping for the Böhm–Wilking cones `Ccone a b p = ℓ_{a,b}(Dpic p)` and their strict versions
`CconeS a b p = ℓ_{a,b}(DpicS p)` (`Strict.lean`):

* the round-sphere tensor: `ric (Iso n) = (n-1)·id`, `scal (Iso n) = n(n-1)`,
  `ℓ_{a,b}(Iso n) = (1 + 2a(n-1)) • Iso n`, and `Iso n` satisfies `RicPinch p` for `p ≤ 1`;
* linearity of `ric`, `ric0`, `scalAlg`, `knProd` and `ℓ`;
* the scaling laws `scal (ℓ_{a,b} R) = (1 + 2a(n-1)) scal R` and
  `Ric₀ (ℓ_{a,b} R) = (1 + (n-2)b) Ric₀ R` (the second one for algebraic curvature tensors);
* injectivity of `ℓ_{a,b}` in the range of interest, and hence the description of the *strict* cone
  as an `Iso`-translate of the closed cone:
  `CconeS a (1/2) p = {Y | ∃ c > 0, Y - c • Iso n ∈ Ccone a (1/2) p}`.

These are the pieces of the reduction of `Ccone_transversal_a` to the (deep) transversality
statement of Brendle–Schoen Prop. 14 / Böhm–Wilking Lemma 3.5.
-/

namespace Work.Diff.Alg.Pinch

open Finset Submission.Diff.Alg

variable {n : ℕ}

/-! ## Linearity -/

lemma ric_add (A B : Curv4 n) (i j : Fin n) : ric (A + B) i j = ric A i j + ric B i j := by
  simp only [ric, Pi.add_apply, Finset.sum_add_distrib]

lemma ric_smul (c : ℝ) (R : Curv4 n) (i j : Fin n) : ric (c • R) i j = c * ric R i j := by
  simp only [ric, Pi.smul_apply, smul_eq_mul, Finset.mul_sum]

lemma scalAlg_add (A B : Curv4 n) : scalAlg (A + B) = scalAlg A + scalAlg B := by
  simp only [scalAlg, Pi.add_apply, Finset.sum_add_distrib]

lemma scalAlg_smul (c : ℝ) (R : Curv4 n) : scalAlg (c • R) = c * scalAlg R := by
  simp only [scalAlg, Pi.smul_apply, smul_eq_mul, Finset.mul_sum]

lemma scalAlg_zero : scalAlg (0 : Curv4 n) = 0 := by simp [scalAlg]

lemma ric0_add (A B : Curv4 n) : ric0 (A + B) = ric0 A + ric0 B := by
  funext i j
  simp only [ric0, Pi.add_apply]
  rw [ric_add, scalAlg_add]
  ring

lemma ric0_smul (c : ℝ) (R : Curv4 n) : ric0 (c • R) = c • ric0 R := by
  funext i j
  simp only [ric0, Pi.smul_apply, smul_eq_mul]
  rw [ric_smul, scalAlg_smul]
  ring

lemma knProd_add_left (A A' B : Fin n → Fin n → ℝ) :
    knProd (A + A') B = knProd A B + knProd A' B := by
  funext i j k l
  simp only [knProd, Pi.add_apply]
  ring

lemma knProd_smul_left (c : ℝ) (A B : Fin n → Fin n → ℝ) :
    knProd (c • A) B = c • knProd A B := by
  funext i j k l
  simp only [knProd, Pi.smul_apply, smul_eq_mul]
  ring

lemma knProd_zero_left (B : Fin n → Fin n → ℝ) : knProd (0 : Fin n → Fin n → ℝ) B = 0 := by
  funext i j k l
  simp [knProd]

lemma ell_add (a b : ℝ) (A B : Curv4 n) : ell a b (A + B) = ell a b A + ell a b B := by
  simp only [ell, ric0_add, scalAlg_add, knProd_add_left]
  rw [smul_add, mul_add, add_smul]
  module

lemma ell_smul (a b c : ℝ) (R : Curv4 n) : ell a b (c • R) = c • ell a b R := by
  have h1 : (a / (n : ℝ) * (c * scalAlg R)) = c * (a / (n : ℝ) * scalAlg R) := by ring
  have h2 : b * c = c * b := by ring
  simp only [ell, ric0_smul, scalAlg_smul, knProd_smul_left]
  rw [smul_add, smul_add, smul_smul, smul_smul, h1, h2]
  simp only [smul_smul]

lemma ell_neg (a b : ℝ) (R : Curv4 n) : ell a b (-R) = - ell a b R := by
  have h := ell_smul a b (-1) R
  simpa using h

lemma ell_sub (a b : ℝ) (A B : Curv4 n) : ell a b (A - B) = ell a b A - ell a b B := by
  rw [sub_eq_add_neg, ell_add, ell_neg, sub_eq_add_neg]

/-! ## The round-sphere tensor -/

lemma Iso_algCurv (n : ℕ) : IsAlgCurv (Iso n) :=
  ⟨fun i j k l => by
     simp only [Iso]
     by_cases h1 : i = k <;> by_cases h2 : i = l <;> by_cases h3 : j = k <;>
       by_cases h4 : j = l <;> by_cases h5 : i = j <;> by_cases h6 : k = l <;>
       simp_all [eq_comm],
   fun i j k l => by
     simp only [Iso]
     by_cases h1 : i = k <;> by_cases h2 : i = l <;> by_cases h3 : j = k <;>
       by_cases h4 : j = l <;> by_cases h5 : i = j <;> by_cases h6 : k = l <;>
       simp_all [eq_comm],
   fun i j k l => by
     simp only [Iso]
     by_cases h1 : i = k <;> by_cases h2 : i = l <;> by_cases h3 : j = k <;>
       by_cases h4 : j = l <;> by_cases h5 : i = j <;> by_cases h6 : k = l <;>
       simp_all [eq_comm]⟩

lemma ric_iso (n : ℕ) (i j : Fin n) : ric (Iso n) i j = ((n : ℝ) - 1) * id2 n i j := by
  have hterm : ∀ k : Fin n, Iso n k i k j = id2 n i j - id2 n k j * id2 n i k := by
    intro k; rw [Iso_eq_id2]; simp [id2]
  simp only [ric, hterm, Finset.sum_sub_distrib]
  rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  have h2 : (∑ k, id2 n k j * id2 n i k) = id2 n i j := by
    rw [show (∑ k, id2 n k j * id2 n i k) = ∑ k, id2 n i k * id2 n k j from
      Finset.sum_congr rfl (fun k _ => by rw [mul_comm])]
    exact sum_id2_mul_id2 i j
  rw [h2]; ring

lemma scalAlg_iso (n : ℕ) : scalAlg (Iso n) = (n : ℝ) * ((n : ℝ) - 1) := by
  have hii : (∑ i : Fin n, id2 n i i) = (n : ℝ) := by
    simp [id2, Finset.sum_const, nsmul_eq_mul]
  have hterm : ∀ i j : Fin n, Iso n i j i j = id2 n i i * id2 n j j - id2 n i j * id2 n j i := by
    intro i j; rw [Iso_eq_id2]
  simp only [scalAlg, hterm, Finset.sum_sub_distrib]
  have h1 : (∑ x : Fin n, ∑ x_1 : Fin n, id2 n x x * id2 n x_1 x_1) = (n : ℝ) * (n : ℝ) := by
    rw [← Finset.sum_mul_sum, hii]
  have h2 : (∑ i, ∑ j, id2 n i j * id2 n j i) = (n : ℝ) := by
    rw [show (∑ i, ∑ j, id2 n i j * id2 n j i) = ∑ i, id2 n i i from
      Finset.sum_congr rfl (fun i _ => sum_id2_mul_id2 i i)]
    exact hii
  rw [h1, h2]; ring

lemma knProd_id2_id2 (n : ℕ) : knProd (id2 n) (id2 n) = (2 : ℝ) • Iso n := by
  funext i j k l
  simp only [knProd, Iso_eq_id2, Pi.smul_apply, smul_eq_mul]
  ring

lemma ric0_iso (n : ℕ) : ric0 (Iso n) = 0 := by
  rcases Nat.eq_zero_or_pos n with h | h
  · subst h; funext i; exact i.elim0
  · have hn : (n : ℝ) ≠ 0 := by exact_mod_cast (Nat.pos_iff_ne_zero.mp h)
    funext i j
    simp only [Pi.zero_apply]
    rw [ric0, ric_iso, scalAlg_iso]
    field_simp
    ring

lemma ell_iso (n : ℕ) (a b : ℝ) :
    ell a b (Iso n) = (1 + 2 * a * ((n : ℝ) - 1)) • Iso n := by
  rw [ell, ric0_iso, knProd_zero_left, smul_zero, add_zero, knProd_id2_id2, scalAlg_iso,
    smul_smul]
  rcases Nat.eq_zero_or_pos n with h | h
  · subst h; simp
  · have hn : (n : ℝ) ≠ 0 := by exact_mod_cast (Nat.pos_iff_ne_zero.mp h)
    have hsc : a / (n : ℝ) * ((n : ℝ) * ((n : ℝ) - 1)) * 2 = 2 * a * ((n : ℝ) - 1) := by
      field_simp
    rw [hsc, add_smul, one_smul]

lemma ricPinch_iso (n : ℕ) {p : ℝ} (hp : p ≤ 1) : RicPinch (n := n) p (Iso n) := by
  intro v
  have hsum : (∑ i, ∑ j, id2 n i j * v i * v j) = ∑ i, v i * v i := by
    apply Finset.sum_congr rfl; intro i _
    rw [show (∑ j, id2 n i j * v i * v j) = v i * (∑ j, id2 n i j * v j) from by
      rw [Finset.mul_sum]
      exact Finset.sum_congr rfl (fun j _ => by ring)]
    rw [ellinv_sum_id2_mul]
  have hricv : (∑ i, ∑ j, ric (Iso n) i j * v i * v j)
      = ((n : ℝ) - 1) * (∑ i, v i * v i) := by
    rw [show (∑ i, ∑ j, ric (Iso n) i j * v i * v j)
        = ∑ i, ∑ j, ((n : ℝ) - 1) * (id2 n i j * v i * v j) from
      Finset.sum_congr rfl (fun i _ => Finset.sum_congr rfl (fun j _ => by
        rw [ric_iso]; ring))]
    rw [show (∑ i, ∑ j, ((n : ℝ) - 1) * (id2 n i j * v i * v j))
        = ((n : ℝ) - 1) * ∑ i, ∑ j, id2 n i j * v i * v j from by
      rw [Finset.mul_sum]
      exact Finset.sum_congr rfl (fun i _ =>
        (Finset.mul_sum (Finset.univ : Finset (Fin n))
          (fun j => id2 n i j * v i * v j) ((n : ℝ) - 1)).symm)]
    rw [hsum]
  rw [scalAlg_iso, hricv]
  rcases Nat.eq_zero_or_pos n with h0 | hpos
  · subst h0
    simp
  · have hn : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hpos
    have hS : (0 : ℝ) ≤ ∑ i, v i * v i := Finset.sum_nonneg (fun i _ => mul_self_nonneg _)
    have hkey : p * ((n : ℝ) * ((n : ℝ) - 1)) / (n : ℝ) = p * ((n : ℝ) - 1) := by
      field_simp
    rw [hkey]
    have hn1 : (0 : ℝ) ≤ (n : ℝ) - 1 := by
      have h1 : (1 : ℕ) ≤ n := hpos
      have h2 : (1 : ℝ) ≤ (n : ℝ) := by exact_mod_cast h1
      linarith
    have hnn : (0 : ℝ) ≤ (1 - p) * ((n : ℝ) - 1) * (∑ i, v i * v i) :=
      mul_nonneg (mul_nonneg (by linarith) hn1) hS
    nlinarith [hnn]

/-! ## Traces and the scaling laws -/

lemma sum_ric_diag (R : Curv4 n) : (∑ i, ric R i i) = scalAlg R := by
  simp only [ric, scalAlg]
  rw [Finset.sum_comm]

lemma sum_ric0_diag (R : Curv4 n) : (∑ i, ric0 R i i) = 0 := by
  rcases Nat.eq_zero_or_pos n with hn | hn
  · subst hn; simp
  · have hn' : (n : ℝ) ≠ 0 := by exact_mod_cast (Nat.pos_iff_ne_zero.mp hn)
    have h1 : (∑ i, ric0 R i i)
        = (∑ i, ric R i i) - (scalAlg R / (n : ℝ)) * (∑ i, id2 n i i) := by
      simp only [ric0, Finset.sum_sub_distrib]
      rw [Finset.mul_sum]
    rw [h1, sum_ric_diag]
    have h2 : (∑ i : Fin n, id2 n i i) = (n : ℝ) := by
      simp [id2, Finset.sum_const, nsmul_eq_mul]
    rw [h2]
    field_simp
    ring

lemma scalAlg_knProd_ric0 (R : Curv4 n) : scalAlg (knProd (ric0 R) (id2 n)) = 0 := by
  rw [scalAlg_knProd]
  have h1 : (∑ i, ric0 R i i) = 0 := sum_ric0_diag R
  have h2 : (∑ i, ∑ j, ric0 R i j * id2 n j i) = 0 := by
    rw [show (∑ i, ∑ j, ric0 R i j * id2 n j i) = ∑ i, ric0 R i i from
      Finset.sum_congr rfl (fun i _ => ellinv_sum_mul_id2 (fun j => ric0 R i j) i)]
    exact h1
  rw [h1, h2]; ring

lemma scalAlg_ell (a b : ℝ) (R : Curv4 n) :
    scalAlg (ell a b R) = (1 + 2 * ((n : ℝ) - 1) * a) * scalAlg R := by
  rw [ell, scalAlg_add, scalAlg_add, scalAlg_smul, scalAlg_smul, scalAlg_knProd_ric0,
    ellinv_scalAlg_knProd_id2_id2]
  rcases Nat.eq_zero_or_pos n with hn | hn
  · subst hn
    rw [show scalAlg R = 0 from by simp [scalAlg]]
    ring
  · have hn' : (n : ℝ) ≠ 0 := by exact_mod_cast (Nat.pos_iff_ne_zero.mp hn)
    field_simp
    ring

lemma ric_knProd_ric0_id2 (R : Curv4 n) (i j : Fin n) :
    ric (knProd (ric0 R) (id2 n)) i j = ((n : ℝ) - 2) * ric0 R i j := by
  rw [ric_knProd_id2, sum_ric0_diag]
  ring

lemma ric_ellAux (a b : ℝ) (R : Curv4 n) (i j : Fin n) :
    ric (ell a b R) i j = (1 + ((n : ℝ) - 2) * b) * ric0 R i j
      + (1 + 2 * ((n : ℝ) - 1) * a) * (scalAlg R / (n : ℝ)) * id2 n i j := by
  have h1 : ric (ell a b R) i j = ric R i j + b * (((n : ℝ) - 2) * ric0 R i j)
      + (a / (n : ℝ) * scalAlg R) * ((2 * (n : ℝ) - 2) * id2 n i j) := by
    rw [ell, ric_add, ric_add, ric_smul, ric_smul, ric_knProd_ric0_id2,
      ellinv_ric_knProd_id2_id2]
  rw [h1, show ric R i j = ric0 R i j + (scalAlg R / (n : ℝ)) * id2 n i j from by
      rw [ric0]; ring]
  rcases Nat.eq_zero_or_pos n with hn | hn
  · subst hn; exact i.elim0
  · have hn' : (n : ℝ) ≠ 0 := by exact_mod_cast (Nat.pos_iff_ne_zero.mp hn)
    field_simp
    ring

lemma ric0_ell (a b : ℝ) (R : Curv4 n) :
    ric0 (ell a b R) = (1 + ((n : ℝ) - 2) * b) • ric0 R := by
  rcases Nat.eq_zero_or_pos n with hn | hn
  · subst hn; funext i; exact i.elim0
  · have hn' : (n : ℝ) ≠ 0 := by exact_mod_cast (Nat.pos_iff_ne_zero.mp hn)
    funext i j
    rw [ric0, ric_ellAux, scalAlg_ell]
    simp only [Pi.smul_apply, smul_eq_mul]
    field_simp
    ring

lemma ric_zeroAux (i j : Fin n) : ric (0 : Curv4 n) i j = 0 := by
  simp only [ric, Pi.zero_apply, mul_zero, Finset.sum_const_zero]

lemma ric0_zero : ric0 (0 : Curv4 n) = 0 := by
  funext i j
  have h1 : scalAlg (0 : Curv4 n) = 0 := by
    simp only [scalAlg, Pi.zero_apply, mul_zero, Finset.sum_const_zero]
  simp only [ric0, Pi.zero_apply, ric_zeroAux, h1, zero_div, zero_mul, sub_zero]

/-! ## Injectivity -/

lemma ell_injective (a b : ℝ) (h1 : 1 + 2 * ((n : ℝ) - 1) * a ≠ 0)
    (h2 : 1 + ((n : ℝ) - 2) * b ≠ 0) : Function.Injective (ell (n := n) a b) := by
  intro X Y hXY
  rcases Nat.eq_zero_or_pos n with hn | hn
  · subst hn
    funext i; exact i.elim0
  · have hZ : ell a b (X - Y) = 0 := by rw [ell_sub, hXY, sub_self]
    have hs : scalAlg (X - Y) = 0 := by
      have hc := congrArg scalAlg hZ
      simp only [scalAlg_zero] at hc
      rw [scalAlg_ell] at hc
      exact (mul_eq_zero.mp hc).resolve_left h1
    have hr : ric0 (X - Y) = 0 := by
      have hc := congrArg ric0 hZ
      rw [ric0_ell, ric0_zero] at hc
      funext i j
      have hcij : (1 + ((n : ℝ) - 2) * b) * ric0 (X - Y) i j = 0 := by
        have h' := congrFun (congrFun hc i) j
        simpa [Pi.smul_apply, smul_eq_mul] using h'
      exact (mul_eq_zero.mp hcij).resolve_left h2
    have hfin : X - Y = 0 := by
      have h := hZ
      rw [ell, hr, hs] at h
      simpa [knProd_zero_left] using h
    rwa [sub_eq_zero] at hfin

/-! ## `RicPinch` is a closed convex cone -/

lemma RicPinch_add {p : ℝ} {A B : Curv4 n} (hA : RicPinch p A) (hB : RicPinch p B) :
    RicPinch p (A + B) := by
  intro v
  have h1 := hA v
  have h2 := hB v
  have hs : scalAlg (A + B) = scalAlg A + scalAlg B := scalAlg_add A B
  have hr : (∑ i, ∑ j, ric (A + B) i j * v i * v j)
      = (∑ i, ∑ j, ric A i j * v i * v j)
        + (∑ i, ∑ j, ric B i j * v i * v j) := by
    simp only [ric_add, add_mul, Finset.sum_add_distrib]
  rw [hs, hr]
  have hsplit : p * (scalAlg A + scalAlg B) / (n : ℝ) * (∑ i, v i * v i)
      = p * scalAlg A / (n : ℝ) * (∑ i, v i * v i)
        + p * scalAlg B / (n : ℝ) * (∑ i, v i * v i) := by ring
  rw [hsplit]
  linarith

lemma RicPinch_smul {p c : ℝ} (hc : 0 ≤ c) {A : Curv4 n} (hA : RicPinch p A) :
    RicPinch p (c • A) := by
  intro v
  have h := hA v
  have hs : scalAlg (c • A) = c * scalAlg A := scalAlg_smul c A
  have hr : (∑ i, ∑ j, ric (c • A) i j * v i * v j)
      = c * (∑ i, ∑ j, ric A i j * v i * v j) := by
    simp only [ric_smul]
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl; intro i _
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl; intro j _
    ring
  rw [hs, hr]
  have hsplit : p * (c * scalAlg A) / (n : ℝ) * (∑ i, v i * v i)
      = c * (p * scalAlg A / (n : ℝ) * (∑ i, v i * v i)) := by ring
  rw [hsplit]
  exact mul_le_mul_of_nonneg_left h hc

/-! ## The strict cone is an `Iso`-translate of the closed cone -/

lemma DpicS_subset_Dpic {p : ℝ} (hp : p ≤ 1) {R : Curv4 n}
    (h : R ∈ DpicS (n := n) p) : R ∈ Dpic (n := n) p := by
  obtain ⟨hR, ⟨ε₁, hε₁, hP⟩, ⟨ε₂, hε₂, hQ⟩⟩ := h
  refine ⟨hR, ?_, ?_⟩
  · have : R = (R - ε₁ • Iso n) + ε₁ • Iso n := by abel
    rw [this]
    exact Cone.inPIC2_add hP (Cone.inPIC2_smul (Cone.inPIC2_iso n) hε₁.le)
  · have : R = (R - ε₂ • Iso n) + ε₂ • Iso n := by abel
    rw [this]
    exact RicPinch_add hQ (RicPinch_smul hε₂.le (ricPinch_iso n hp))

lemma mem_CconeS_iff (a b p : ℝ) (hp : p ≤ 1) (hpos : 0 < 1 + 2 * a * ((n : ℝ) - 1))
    (Y : Curv4 n) :
    Y ∈ CconeS (n := n) a b p ↔ ∃ c : ℝ, 0 < c ∧ Y - c • Iso n ∈ Ccone (n := n) a b p := by
  constructor
  · rintro ⟨X, hX, rfl⟩
    obtain ⟨hXa, ⟨ε₁, hε₁, hP⟩, ⟨ε₂, hε₂, hQ⟩⟩ := hX
    set ε : ℝ := min ε₁ ε₂ with hεdef
    have hε : 0 < ε := lt_min hε₁ hε₂
    have hεle₁ : ε ≤ ε₁ := min_le_left _ _
    have hεle₂ : ε ≤ ε₂ := min_le_right _ _
    -- `X - ε • Iso n` is still in `Dpic p`
    have hmem : X - ε • Iso n ∈ Dpic (n := n) p := by
      have halg : IsAlgCurv (X - ε • Iso n) := by
        have h := isAlgCurv_add hXa (isAlgCurv_smul (-ε) (Iso_algCurv n))
        simpa [sub_eq_add_neg, neg_smul] using h
      have hpic : InPIC2 (X - ε • Iso n) := by
        have hsplit : X - ε • Iso n = (X - ε₁ • Iso n) + (ε₁ - ε) • Iso n := by module
        rw [hsplit]
        exact Cone.inPIC2_add hP
          (Cone.inPIC2_smul (Cone.inPIC2_iso n) (by linarith))
      have hric : RicPinch p (X - ε • Iso n) := by
        have hsplit : X - ε • Iso n = (X - ε₂ • Iso n) + (ε₂ - ε) • Iso n := by module
        rw [hsplit]
        exact RicPinch_add hQ (RicPinch_smul (by linarith) (ricPinch_iso n hp))
      exact ⟨halg, hpic, hric⟩
    refine ⟨ε * (1 + 2 * a * ((n : ℝ) - 1)), mul_pos hε hpos, ?_⟩
    refine ⟨X - ε • Iso n, hmem, ?_⟩
    rw [ell_sub, ell_smul, ell_iso, smul_smul]
  · rintro ⟨c, hc, X, hX, hXeq⟩
    -- `Y = ell a b X + c • Iso n = ell a b (X + δ • Iso n)` with `δ = c/(1+2a(n-1))`
    have hne : 1 + 2 * a * ((n : ℝ) - 1) ≠ 0 := ne_of_gt hpos
    set δ : ℝ := c / (1 + 2 * a * ((n : ℝ) - 1)) with hδdef
    have hδ : 0 < δ := div_pos hc hpos
    refine ⟨X + δ • Iso n, ⟨?_, ?_, ?_⟩, ?_⟩
    · exact isAlgCurv_add hX.1 (isAlgCurv_smul δ (Iso_algCurv n))
    · -- StrictInPIC2
      refine ⟨δ, hδ, ?_⟩
      have : X + δ • Iso n - δ • Iso n = X := by abel
      rw [this]
      exact hX.2.1
    · refine ⟨δ, hδ, ?_⟩
      have : X + δ • Iso n - δ • Iso n = X := by abel
      rw [this]
      exact hX.2.2
    · have hc' : ell a b (δ • Iso n) = c • Iso n := by
        rw [ell_smul, ell_iso, smul_smul]
        congr 1
        rw [hδdef]
        field_simp
      rw [ell_add, hc', hXeq]
      abel

end Work.Diff.Alg.Pinch
