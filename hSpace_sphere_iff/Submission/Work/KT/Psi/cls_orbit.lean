import Mathlib
import Submission.Work.KT.Defs
import Submission.Work.KT.Psi.Basic
import Submission.Work.KT.Psi.OrbitBasic
import Submission.Work.KT.Psi.OrbitFacts
import Submission.Work.KT.Psi.OrbitCrux

/-!
# `Work.KT.Psi.cls_orbit` — the free-orbit lemma

`g` of order dividing `k`, `F` an idempotent whose `k` conjugates `g^i F g^{-i}` are pairwise
orthogonal, `P` an idempotent commuting with `g` and `F`.  Then for every `k`-th root of unity
`λ`, the `λ`-eigenpart `R = P · O · E_λ` of `P · (orbit sum of F)` is Murray–von Neumann
equivalent to `G = P F` (all eigenspaces of an induced module are isomorphic), hence they have the
same class in `K₀`.

The two structural inputs are proved in the sibling files:
* `OrbitFacts`: `O = Σ_{i<k} g^i F g^{k-i}` is idempotent, `F O = F`, and `O` commutes with `g`
  and with `P`;
* `OrbitCrux`: the two "orbit ♢ spectral projector" identities
  `F O E F = k⁻¹ F` and `O E F O E = k⁻¹ (O E)`.

The Murray–von Neumann witnesses are explicit: with `R = P·O·E_λ`, `G = P F`,
`a = R·G` and `b = k·G·R` satisfy `b a = G`, `a b = R`.
-/

namespace Work.KT.Psi

open Matrix Finset

noncomputable section

variable {M : Type} [Ring M] [Algebra ℂ M]

/-- `a * (b * x) = b * (a * x)` when `a` and `b` commute. -/
lemma cls_orbit_swap {a b x : M} (h : a * b = b * a) : a * (b * x) = b * (a * x) := by
  rw [← mul_assoc, ← mul_assoc, h]

/-- `a * (b * c) = (b * c) * a` when `a` commutes with both `b` and `c`. -/
lemma cls_orbit_mul_swap_mul {a b c : M} (hab : a * b = b * a) (hac : a * c = c * a) :
    a * (b * c) = (b * c) * a := by
  conv_lhs => rw [← mul_assoc, hab, mul_assoc, hac, ← mul_assoc]

/-- **Abstract Murray–von Neumann core.**  Writing `R = P · O · E` (`O` the orbit sum, `E` the
spectral projector) and `G = P F`, the four identities needed for the Murray–von Neumann
equivalence `R ~ G` with witnesses `a = R G`, `b = k G R` hold. -/
theorem cls_orbit_core (k : ℕ) (hk : 0 < k) (P F g : M)
    (hP : P * P = P) (hF : F * F = F) (hg : g ^ k = 1) (hPg : P * g = g * P)
    (hPF : P * F = F * P)
    (horth : ∀ i j : ℕ, i < k → j < k → i ≠ j →
      (g ^ i * F * g ^ (k - i)) * (g ^ j * F * g ^ (k - j)) = 0)
    (lam : ℂ) (hlam : lam ^ k = 1) :
    ((P * (orbSum g F k * orbitSpec lam g k)) * (P * (orbSum g F k * orbitSpec lam g k))
        = P * (orbSum g F k * orbitSpec lam g k)) ∧
    ((P * F) * (P * F) = P * F) ∧
    ((P * F) * (P * (orbSum g F k * orbitSpec lam g k)) * (P * F)
        = algebraMap ℂ M ((k : ℂ)⁻¹) * (P * F)) ∧
    ((P * (orbSum g F k * orbitSpec lam g k)) * (P * F) * (P * (orbSum g F k * orbitSpec lam g k))
        = algebraMap ℂ M ((k : ℂ)⁻¹) * (P * (orbSum g F k * orbitSpec lam g k))) := by
  obtain ⟨hOidem, -, hgO, hPO⟩ := OrbitFacts k hk P F g hF hg hPg hPF horth
  obtain ⟨hcr1, hcr2⟩ := OrbitCrux k hk F g hF hg horth lam hlam
  have hEidem : orbitSpec lam g k * orbitSpec lam g k = orbitSpec lam g k :=
    orbitSpec_idem hk (qg_pow_eq_one hg hlam)
  have hOE : orbSum g F k * orbitSpec lam g k = orbitSpec lam g k * orbSum g F k :=
    (orbitSpec_comm_of (g := g) (X := orbSum g F k) (k := k) hgO).symm
  have hPE : P * orbitSpec lam g k = orbitSpec lam g k * P :=
    (orbitSpec_comm_of (g := g) (X := P) (k := k) hPg.symm).symm
  set Y : M := orbSum g F k * orbitSpec lam g k with hY
  have hYidem : Y * Y = Y := by
    rw [hY]
    have sEO : ∀ x : M,
        orbitSpec lam g k * (orbSum g F k * x) = orbSum g F k * (orbitSpec lam g k * x) :=
      fun x => cls_orbit_swap (x := x) hOE.symm
    have iO : ∀ x : M, orbSum g F k * (orbSum g F k * x) = orbSum g F k * x :=
      fun x => by rw [← mul_assoc, hOidem]
    have iE : ∀ x : M, orbitSpec lam g k * (orbitSpec lam g k * x) = orbitSpec lam g k * x :=
      fun x => by rw [← mul_assoc, hEidem]
    simp only [mul_assoc, sEO, iO, iE, hOidem, hEidem]
  have hPY : P * Y = Y * P := by
    rw [hY]
    exact cls_orbit_mul_swap_mul hPO hPE
  have hYF : Y * F * Y = algebraMap ℂ M ((k : ℂ)⁻¹) * Y := by
    rw [hY]
    conv_lhs => rw [← mul_assoc]
    exact hcr2
  have hFYF : F * Y * F = algebraMap ℂ M ((k : ℂ)⁻¹) * F := by
    rw [hY]
    conv_lhs => rw [← mul_assoc]
    exact hcr1
  have sYP : ∀ x : M, Y * (P * x) = P * (Y * x) := fun x => cls_orbit_swap (x := x) hPY.symm
  have sFP : ∀ x : M, F * (P * x) = P * (F * x) := fun x => cls_orbit_swap (x := x) hPF.symm
  have sPc : ∀ x : M, P * (algebraMap ℂ M ((k : ℂ)⁻¹) * x)
      = algebraMap ℂ M ((k : ℂ)⁻¹) * (P * x) :=
    fun x => cls_orbit_swap (x := x) (Algebra.commutes ((k : ℂ)⁻¹) P).symm
  have iP : ∀ x : M, P * (P * x) = P * x := fun x => by rw [← mul_assoc, hP]
  have hYF' : Y * (F * Y) = algebraMap ℂ M ((k : ℂ)⁻¹) * Y := by rw [← mul_assoc]; exact hYF
  have hFYF' : F * (Y * F) = algebraMap ℂ M ((k : ℂ)⁻¹) * F := by rw [← mul_assoc]; exact hFYF
  refine ⟨?_, ?_, ?_, ?_⟩ <;>
    simp only [mul_assoc, sYP, sFP, sPc, iP, hYidem, hF, hYF', hFYF']

/-- The `A`-scalar action on matrices is the `ℂ`-scalar action. -/
lemma cls_orbit_algMap_smul {A : Type} [Ring A] [Algebra ℂ A] {N : ℕ} (c : ℂ)
    (X : Matrix (Fin N) (Fin N) A) : algebraMap ℂ A c • X = c • X := by
  ext i j
  simp only [Matrix.smul_apply, smul_eq_mul, Algebra.smul_def]

/-- The statement's form of the spectral projector is `orbitSpec lam g k`. -/
lemma cls_orbit_stmtE {A : Type} [Ring A] [Algebra ℂ A] {N k : ℕ} (lam : ℂ)
    (g : Matrix (Fin N) (Fin N) A) :
    algebraMap ℂ A (1 / (k : ℂ)) • (∑ j ∈ Finset.range k, algebraMap ℂ A (lam⁻¹ ^ j) • g ^ j)
      = orbitSpec lam g k := by
  have h1 : ∀ j : ℕ, algebraMap ℂ A (lam⁻¹ ^ j) • g ^ j = qg lam g ^ j := by
    intro j
    rw [qg_pow]
    exact cls_orbit_algMap_smul (lam⁻¹ ^ j) (g ^ j)
  have hsum : (∑ j ∈ Finset.range k, algebraMap ℂ A (lam⁻¹ ^ j) • g ^ j) = geoSum lam g k :=
    Finset.sum_congr rfl (fun j _ => h1 j)
  rw [hsum, cls_orbit_algMap_smul, one_div, orbitSpec]

/-- **Free-orbit result.** `g` of order dividing `k`, `F` an idempotent whose `k` conjugates
`g^i F g^{-i}` are pairwise orthogonal, `P` an idempotent commuting with `g` and `F`.  Then for every
`k`-th root of unity `λ`, the `λ`-eigenpart of `P · (orbit sum of F)` has the class of `P F`
(all eigenspaces of an induced module are isomorphic).  Explicit MvN witnesses: with
`R = P·O·E_λ`, `G = P·F`: `a = R·G`, `b = k·G·R`. -/
theorem cls_orbit (A : Type) [Ring A] [Algebra ℂ A] (hA : ∀ x y : A, x * y = y * x)
    (N k : ℕ) (hk : 0 < k) (P F g : Matrix (Fin N) (Fin N) A)
    (hP : P * P = P) (hF : F * F = F) (hg : g ^ k = 1) (hPg : P * g = g * P) (hPF : P * F = F * P)
    (horth : ∀ i j : ℕ, i < k → j < k → i ≠ j →
      (g ^ i * F * g ^ (k - i)) * (g ^ j * F * g ^ (k - j)) = 0)
    (lam : ℂ) (hlam : lam ^ k = 1) :
    cls (⟨N, P * (∑ i ∈ Finset.range k, g ^ i * F * g ^ (k - i)) *
        (algebraMap ℂ A (1 / (k : ℂ)) •
          ∑ j ∈ Finset.range k, algebraMap ℂ A (lam⁻¹ ^ j) • g ^ j)⟩ : Mat A) =
      cls ⟨N, P * F⟩ := by
  rw [cls_orbit_stmtE, mul_assoc]
  obtain ⟨hRidem, hGidem, hGRG, hRGR⟩ :=
    cls_orbit_core (M := Matrix (Fin N) (Fin N) A) k hk P F g hP hF hg hPg hPF horth lam hlam
  have hkne : (k : ℂ) ≠ 0 := by exact_mod_cast Nat.pos_iff_ne_zero.mp hk
  refine (cls_eq_of_MvN (p := (⟨N, P * F⟩ : Mat A))
    (q := (⟨N, P * (orbSum g F k * orbitSpec lam g k)⟩ : Mat A)) hGidem hRidem ?_).symm
  refine ⟨(P * (orbSum g F k * orbitSpec lam g k)) * (P * F),
    (k : ℂ) • ((P * F) * (P * (orbSum g F k * orbitSpec lam g k))), ?_, ?_⟩
  · rw [smul_mul_assoc]
    have hrr : ((P * F) * (P * (orbSum g F k * orbitSpec lam g k))) *
        ((P * (orbSum g F k * orbitSpec lam g k)) * (P * F)) =
        (P * F) * (P * (orbSum g F k * orbitSpec lam g k)) * (P * F) := by
      rw [← mul_assoc, mul_assoc (P * F) (P * (orbSum g F k * orbitSpec lam g k))
        (P * (orbSum g F k * orbitSpec lam g k)), hRidem]
    rw [hrr, hGRG, ← Algebra.smul_def ((k : ℂ)⁻¹) (P * F), smul_smul, mul_inv_cancel₀ hkne,
      one_smul]
  · rw [mul_smul_comm]
    have hrr : ((P * (orbSum g F k * orbitSpec lam g k)) * (P * F)) *
        ((P * F) * (P * (orbSum g F k * orbitSpec lam g k))) =
        (P * (orbSum g F k * orbitSpec lam g k)) * (P * F) *
          (P * (orbSum g F k * orbitSpec lam g k)) := by
      rw [← mul_assoc, mul_assoc (P * (orbSum g F k * orbitSpec lam g k)) (P * F) (P * F),
        hGidem]
    rw [hrr, hRGR, ← Algebra.smul_def ((k : ℂ)⁻¹)
      (P * (orbSum g F k * orbitSpec lam g k)), smul_smul, mul_inv_cancel₀ hkne, one_smul]

end

end Work.KT.Psi
