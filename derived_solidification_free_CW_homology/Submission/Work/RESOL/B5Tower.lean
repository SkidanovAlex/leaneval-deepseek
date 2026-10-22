/-
AREA RESOL — the telescope of the truncations retracts onto a bounded-above complex.

Given a complex `K`, with the vocabulary of `RESOL/B5TowerDefs.lean`, this file proves the
identities

* `s K ≫ σ K = σ K` (the fold map is invariant under the shift of the telescope),
* `u m ≫ s = u (m+1)`, `u m ≫ σ = 𝟙`, `u m ≫ d_A = d_K ≫ u m` (the coherent inclusion of
  `K.X n` as the `m`-th summand of `A K`),
* `Xsum K n ≫ (1 - s) = u_{M(n+1)} - u_{M n}` (the telescoping identity),
* `α K n ≫ d_A + d_K ≫ α K (n+1) = 0` and
  `α K n ≫ (1-s) + β K n ≫ d_A = d_K ≫ β K (n+1)` (the two components of the coherent section),

then assembles the maps `φ K : T K ⟶ K` (induced by `σ K` and the zero homotopy of
`(1-s) ≫ σ`) and `ψ K : K ⟶ T K`, and proves the retraction identity `ψ K ≫ φ K = 𝟙 K`.

Together with the cofibrancy of `T K` (`RESOL/solidCofibrant_telescope.lean`) and
`RESOL.solidCofibrant_of_retract` this gives that `K` is solid-cofibrant as soon as the
truncations `U m` are — the final step of B5.
-/
import Mathlib
import Submission.Work.RESOL.Basic
import Submission.Work.RESOL.B5TowerDefs

open CategoryTheory Limits LightCondensed
open HomologicalComplex

noncomputable section

namespace Work.RESOL

/-! ## The inclusion `U m ⟶ K` -/

/-- The composite `U m ⟶ U (m+1) ⟶ K` is the inclusion `U m ⟶ K`. -/
lemma Uinc_comp_incl (K : Cpx) (m : ℕ) : Uinc K m ≫ incl K (L (m + 1)) = incl K (L m) := by
  apply Hom.ext
  funext n
  by_cases h : L m ≤ n
  · have h2 : L (m + 1) ≤ n := L_succ_le h
    rw [HomologicalComplex.comp_f, Uinc_f_of_le K h, incl_f_of_le K h2, incl_f_of_le K h,
      Category.assoc, eqToHom_comp_eqToHom_self, Category.comp_id]
  · have hz : (Uinc K m).f n = 0 := Uinc_f_of_not_le K h
    rw [HomologicalComplex.comp_f, hz, zero_comp, incl_f_of_not_le K h]

/-! ## The fold map and the shift of the telescope -/

lemma s_ι (K : Cpx) [HasCoproduct (U K)] (m : ℕ) :
    Sigma.ι (U K) m ≫ s K = Uinc K m ≫ Sigma.ι (U K) (m + 1) :=
  Sigma.ι_comp_desc _ m

lemma σ_ι (K : Cpx) [HasCoproduct (U K)] (m : ℕ) :
    Sigma.ι (U K) m ≫ σ K = incl K (L m) :=
  Sigma.ι_comp_desc _ m

/-- The fold map is compatible with the shift of the telescope. -/
lemma s_comp_σ (K : Cpx) [HasCoproduct (U K)] : s K ≫ σ K = σ K := by
  apply Sigma.hom_ext
  intro m
  rw [← Category.assoc, s_ι, Category.assoc, σ_ι K (m + 1), σ_ι K m]
  exact Uinc_comp_incl K m

lemma sub_comp_σ (K : Cpx) [HasCoproduct (U K)] : sc K ≫ σ K = 0 := by
  rw [sc, Preadditive.sub_comp, Category.id_comp, s_comp_σ, sub_self]

/-! ## The coherent inclusion `u` -/

/-- **The telescoping relation**: `u m ≫ s = u (m+1)` in degrees visible from `U m`. -/
lemma u_comp_s (K : Cpx) [HasCoproduct (U K)] (m : ℕ) (n : ℤ) (h : L m ≤ n) :
    u K m n ≫ (s K).f n = u K (m + 1) n := by
  rw [u_of_le K h, u_of_le K (L_succ_le h), Category.assoc, ← HomologicalComplex.comp_f,
    s_ι, HomologicalComplex.comp_f, Uinc_f_of_le K h]
  simp only [Category.assoc, eqToHom_comp_eqToHom_self_sandwich]

/-- **The section relation**: `u m ≫ σ = 𝟙` whenever the truncation `U m` sees degree `n`. -/
lemma u_comp_σ (K : Cpx) [HasCoproduct (U K)] (m : ℕ) (n : ℤ) (h : L m ≤ n) :
    u K m n ≫ (σ K).f n = 𝟙 (K.X n) := by
  rw [u_of_le K h, Category.assoc, ← HomologicalComplex.comp_f, σ_ι, incl_f_of_le K h,
    eqToHom_comp_eqToHom_self]

/-- **The chain relation**: `u m ≫ d_A = d_K ≫ u m` in degrees visible from `U m`. -/
lemma u_comp_d (K : Cpx) [HasCoproduct (U K)] (m : ℕ) (n : ℤ) (h : L m ≤ n) :
    u K m n ≫ (A K).d n (n + 1) = K.d n (n + 1) ≫ u K m (n + 1) := by
  rw [u_of_le K h, u_of_le K (L_le_succ h), Category.assoc,
    Hom.comm (Sigma.ι (U K) m) n (n + 1), trunc_d_eq K rfl h (L_le_succ h)]
  simp only [Category.assoc, eqToHom_comp_eqToHom_self_sandwich]

/-- The `d`-component of the telescope: it is the `homotopyCofiber.d`. -/
lemma T_d (K : Cpx) [HasCoproduct (U K)] (i j : ℤ) :
    (T K).d i j = homotopyCofiber.d (sc K) i j := rfl

/-! ## The telescoping algebra -/

/-- Telescoping sums with the sign convention used for `Xsum`. -/
lemma sum_range_sub' {G : Type*} [AddCommGroup G] (F : ℕ → G) (r : ℕ) :
    (∑ k ∈ Finset.range r, (F k - F (k + 1))) = F 0 - F r := by
  have h3 : (∑ k ∈ Finset.range r, (F k - F (k + 1)))
      = -∑ k ∈ Finset.range r, (F (k + 1) - F k) := by
    rw [← Finset.sum_neg_distrib]
    exact Finset.sum_congr rfl fun k _ => by abel
  rw [h3, Finset.sum_range_sub]
  abel

/-- **The telescoping identity**: `Xsum ≫ (1 - s) = u_{M(n+1)} - u_{M n}`. -/
lemma Xsum_comp_sc (K : Cpx) [HasCoproduct (U K)] (n : ℤ) :
    Xsum K n ≫ (sc K).f (n + 1) = u K (M (n + 1)) (n + 1) - u K (M n) (n + 1) := by
  have hsum : (∑ k ∈ Finset.range (M n - M (n + 1)),
        u K (M (n + 1) + k) (n + 1) ≫ (s K).f (n + 1))
      = ∑ k ∈ Finset.range (M n - M (n + 1)), u K (M (n + 1) + (k + 1)) (n + 1) :=
    Finset.sum_congr rfl fun k _ => u_comp_s K _ _ (L_add_M n k)
  have h1 : Xsum K n ≫ (sc K).f (n + 1)
      = (∑ k ∈ Finset.range (M n - M (n + 1)), u K (M (n + 1) + k) (n + 1))
        - ∑ k ∈ Finset.range (M n - M (n + 1)),
            u K (M (n + 1) + (k + 1)) (n + 1) := by
    rw [show (sc K).f (n + 1) = 𝟙 ((A K).X (n + 1)) - (s K).f (n + 1) from rfl,
      Preadditive.comp_sub, Category.comp_id, Xsum, Ysum, Preadditive.sum_comp, hsum]
  rw [h1, ← Finset.sum_sub_distrib, sum_range_sub', Nat.add_zero,
    Nat.add_sub_cancel' (M_succ_le n)]

/-- **The chain identity for the telescoping sum**: `Ysum ≫ d_A = d_K ≫ Ysum`. -/
lemma Ysum_comp_d (K : Cpx) [HasCoproduct (U K)] (n m : ℤ)
    (hm : ∀ k : ℕ, L (M (n + 1) + k) ≤ m) :
    Ysum K n m ≫ (A K).d m (m + 1) = K.d m (m + 1) ≫ Ysum K n (m + 1) := by
  rw [Ysum, Preadditive.sum_comp, Preadditive.comp_sum]
  exact Finset.sum_congr rfl fun k _ => u_comp_d K _ m (hm k)

/-- The hypothesis of `Ysum_comp_d` in the two degrees needed. -/
lemma L_add_M' (n m : ℤ) (hm : n + 1 ≤ m) (k : ℕ) : L (M (n + 1) + k) ≤ m :=
  le_trans (L_add_M n k) hm

/-- **Equation (a)**: `α ≫ d_A + d_K ≫ α = 0`. -/
lemma α_comp_d (K : Cpx) [HasCoproduct (U K)] (n : ℤ) :
    α K n ≫ (A K).d (n + 1) ((n + 1) + 1) + K.d n (n + 1) ≫ α K (n + 1) = 0 := by
  have h0 : K.d n (n + 1) ≫ K.d (n + 1) ((n + 1) + 1) = 0 :=
    K.d_comp_d n (n + 1) ((n + 1) + 1)
  have h := Ysum_comp_d K n (n + 1) (L_add_M' n (n + 1) le_rfl)
  show (K.d n (n + 1) ≫ Xsum K n) ≫ (A K).d (n + 1) ((n + 1) + 1)
      + K.d n (n + 1) ≫ (K.d (n + 1) ((n + 1) + 1) ≫ Xsum K (n + 1)) = 0
  rw [Category.assoc, show Xsum K n = Ysum K n (n + 1) from rfl, h]
  simp only [← Category.assoc, h0, zero_comp, add_zero]

/-- **Equation (b)**: `α ≫ (1-s) + β ≫ d_A = d_K ≫ β`. -/
lemma α_comp_sc_add (K : Cpx) [HasCoproduct (U K)] (n : ℤ) :
    α K n ≫ (sc K).f (n + 1) + β K n ≫ (A K).d n (n + 1) = K.d n (n + 1) ≫ β K (n + 1) := by
  have h := Xsum_comp_sc K n
  have h2 := u_comp_d K (M n) n (L_M n)
  show (K.d n (n + 1) ≫ Xsum K n) ≫ (sc K).f (n + 1)
      + u K (M n) n ≫ (A K).d n (n + 1) = K.d n (n + 1) ≫ u K (M (n + 1)) (n + 1)
  rw [Category.assoc, h, h2, Preadditive.comp_sub]
  abel

/-! ## The maps `φ` and `ψ` -/

/-- The map `T K ⟶ K` induced by the fold map `σ` and the zero homotopy of `(1-s) ≫ σ`. -/
abbrev φ (K : Cpx) [HasCoproduct (U K)] : T K ⟶ K :=
  homotopyCofiber.desc (sc K) (σ K) (Homotopy.ofEq (sub_comp_σ K))

lemma φ_f (K : Cpx) [HasCoproduct (U K)] (n : ℤ) :
    (φ K).f n = homotopyCofiber.sndX (sc K) n ≫ (σ K).f n := by
  rw [φ, homotopyCofiber.desc_f (sc K) (σ K) (Homotopy.ofEq (sub_comp_σ K)) n (n + 1)
      (rel_up n), Homotopy.ofEq_hom]
  simp only [Pi.zero_apply, comp_zero, zero_add]

lemma ψ_fst (K : Cpx) [HasCoproduct (U K)] (n : ℤ) :
    ψf K n ≫ homotopyCofiber.fstX (sc K) n (n + 1) (rel_up n) = α K n := by
  rw [ψf, Preadditive.add_comp]
  simp only [Category.assoc]
  rw [homotopyCofiber.inlX_fstX, homotopyCofiber.inrX_fstX, Category.comp_id,
    comp_zero, add_zero]

lemma ψ_snd (K : Cpx) [HasCoproduct (U K)] (n : ℤ) :
    ψf K n ≫ homotopyCofiber.sndX (sc K) n = β K n := by
  rw [ψf, Preadditive.add_comp]
  simp only [Category.assoc]
  rw [homotopyCofiber.inlX_sndX, homotopyCofiber.inrX_sndX, comp_zero, comp_zero,
    Category.comp_id, zero_add]

/-- The "coherent section" `K ⟶ T K` of the fold map. -/
def ψ (K : Cpx) [HasCoproduct (U K)] : K ⟶ T K where
  f := ψf K
  comm' i n hin := by
    rw [ComplexShape.up_Rel] at hin
    obtain rfl : n = i + 1 := by omega
    rw [T_d]
    apply homotopyCofiber.ext_to_X (sc K) (i + 1) ((i + 1) + 1) (rel_up (i + 1))
    · have hL : (ψf K i ≫ homotopyCofiber.d (sc K) i (i + 1)) ≫
            homotopyCofiber.fstX (sc K) (i + 1) ((i + 1) + 1) (rel_up (i + 1))
          = -(α K i ≫ (A K).d (i + 1) ((i + 1) + 1)) := by
        rw [Category.assoc, homotopyCofiber.d_fstX (sc K) i (i + 1) ((i + 1) + 1)
            (rel_up i) (rel_up (i + 1)), Preadditive.comp_neg, ← Category.assoc, ψ_fst]
      have hR : (K.d i (i + 1) ≫ ψf K (i + 1)) ≫
            homotopyCofiber.fstX (sc K) (i + 1) ((i + 1) + 1) (rel_up (i + 1))
          = K.d i (i + 1) ≫ α K (i + 1) := by
        rw [Category.assoc, ψ_fst]
      rw [hL, hR, neg_eq_iff_add_eq_zero]
      exact α_comp_d K i
    · have hL : (ψf K i ≫ homotopyCofiber.d (sc K) i (i + 1)) ≫
            homotopyCofiber.sndX (sc K) (i + 1)
          = α K i ≫ (sc K).f (i + 1) + β K i ≫ (A K).d i (i + 1) := by
        rw [Category.assoc, homotopyCofiber.d_sndX (sc K) i (i + 1) (rel_up i),
          Preadditive.comp_add, ← Category.assoc, ← Category.assoc, ψ_fst, ψ_snd]
      have hR : (K.d i (i + 1) ≫ ψf K (i + 1)) ≫ homotopyCofiber.sndX (sc K) (i + 1)
          = K.d i (i + 1) ≫ β K (i + 1) := by
        rw [Category.assoc, ψ_snd]
      rw [hL, hR]
      exact α_comp_sc_add K i

@[simp]
lemma ψ_f_apply (K : Cpx) [HasCoproduct (U K)] (n : ℤ) : (ψ K).f n = ψf K n := rfl

/-- The retraction identity `ψ ≫ φ = 𝟙`. -/
theorem ψ_comp_φ (K : Cpx) [HasCoproduct (U K)] : ψ K ≫ φ K = 𝟙 K := by
  apply Hom.ext
  funext n
  rw [HomologicalComplex.comp_f (ψ K) (φ K) n, HomologicalComplex.id_f,
    φ_f, ψ_f_apply, ← Category.assoc, ψ_snd]
  exact u_comp_σ K (M n) n (L_M n)

end Work.RESOL
