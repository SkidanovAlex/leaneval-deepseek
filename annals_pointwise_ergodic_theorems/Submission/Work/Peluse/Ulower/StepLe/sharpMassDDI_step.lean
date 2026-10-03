import Mathlib
import Submission.Work.Peluse.Ulower.StepLe.ddiSharp.cubeTerm_cons_one
import Submission.Work.Peluse.Ulower.StepLe.ddiSharp.cubeTerm_mul_shift
import Submission.Work.Peluse.Ulower.StepLe.ddiSharp.mixedPhase_cons
import Submission.Work.Peluse.Ulower.StepLe.ddiSharp.one.Defs
import Submission.Work.Peluse.Ulower.StepLe.sharpStep.thetaFan
import Submission.Work.Peluse.Ulower.StepLe.sharpStep.rowCol_transpose
import Submission.Work.Peluse.Ulower.StepLe.sharpStep.hypoMass_succ_row

namespace Work.Peluse.Ulower.StepLe

/-
**The dimension step of the mass form of the interchange** (`SharpMassDDI` in
`StepLe/ddiSharp/Defs.lean`; the full derivation of this step, with the exact exponents, is in
`NOTES_CRITICAL_PATH.md`, section "What is NOT needed *as such*").  Proving
`SharpMassDDI 1` + this step for all `σ` gives `SharpMassDDI σ` for all `σ`, hence — through
`StepLe/hasInterchangeL_of_sharpMass.lean` — the lossy interchange `HasInterchangeL P`, hence
`StepLe.blindConvertK2`, hence the target `Work.Peluse.Ulower.degree_lowering_v2`.

This is the cleanest formulation of the crux: everything is a **mass** (`∑`, not an average), so the
two-level Cauchy–Schwarz needs no level-uniformity bookkeeping; the levels only enter the exponent
arithmetic.  Concretely, with `A_{(a,b)} := hypoMass σ B (K^{(a,b)}) (rowFibre H a b) (φ_ab)`,
`K^{(a,b)}_{(z,z')}(y) := star (G z (y+a)) * G z' (y+b)` on `Z × Z`, `φ_ab(q) := φ (cons a q.1)
(cons b q.2)`, and `H₂(k̄) := hypoMass 1 B (ct(k̄.2.1,k̄.2.2) ∘ G) (colFibre H k̄) (φ̄)` with
`φ̄(a,b) := mixedPhase φ_ab k̄` (the *mixed phase of the row phase* — see
`NOTES_dualDiffStep_PHASE_TRICK.md`; this is what makes the two instances match, together with
`cubeTerm_cons_pair`, `cubeTerm_cons_one`, `cubeTerm_mean_cons`, `mixedPhase_cons`):

* `hypoMass (σ+1) B G H φ = ∑_{(a,b)∈[1,D]²} A_{(a,b)}` (row decomposition, row form);
* `A_{(a,b)}^{2^σ} ≤ C D^{d_σ} concMass σ D B (K^{(a,b)}) (rowFibre H a b) (φ_ab)` (`IH`);
* `H₂(k̄)² ≤ C₁ D^{d₁} concMass 1 D B (ct ∘ G) (colFibre H k̄) (φ̄)` (`IH1`, `d₁ := 1`);
* **transposition (free in the mass form)**: `∑_{k̄} H₂(k̄) = ∑_{(a,b)} concMass σ D B (K^{(a,b)})
  (rowFibre H a b) (φ_ab)` and `∑_{k̄} concMass 1 D B (ct ∘ G) (colFibre H k̄) (φ̄) =
  concMass (σ+1) D B G H φ` (both are just swaps of the summation order over incidences
  `k̄ ∈ Θ_σ(rowFibre H a b)`; the index sets are `colFibre`/`rowFibre` respectively, and the
  `(σ+1)`-cube set splits as `Θ_{σ+1}(H) = ⊔_{k̄} Θ_1(colFibre H k̄)`, `sum_ThetaSet_succ`);
* Hölder/power mean with the number `D²` of rows and the number `D^{3σ}` of σ-triples:
  `(∑A)^{2^{σ+1}} ≤ (D²)^{2^{σ+1}-2} (∑A^{2^σ})²` and `(∑_{k̄}H₂(k̄))² ≤ D^{3σ}∑_{k̄}H₂(k̄)²`;
* combining gives `d_{σ+1} = 2 d_σ + 2(2^{σ+1}-2) + 3σ + d₁`, i.e. `d_σ = σ(2^{σ+1}-3)` with
  `d₁ = 1` — exactly the recurrence recorded in `ddiSharp/Defs.lean`.
-/


/-! ## The row and column families of the induction step -/

/-- The bilinear row family: `K^{(a,b)}_{(z,z')}(y) = G z (y + b) · conj (G z' (y + a))`. -/
def Kp {Z : Type} (G : Z → ℤ → ℂ) (ab : (Fin 1 → ℤ) × (Fin 1 → ℤ)) : Z × Z → ℤ → ℂ :=
  fun p y => G p.1 (y + ab.2 0) * star (G p.2 (y + ab.1 0))

/-- The row phase `φ_ab(u,v) = φ (a :: u) (b :: v)`. -/
def phRow {σ : ℕ} (φ : (Fin (σ+1) → ℤ) → (Fin (σ+1) → ℤ) → ℝ)
    (ab : (Fin 1 → ℤ) × (Fin 1 → ℤ)) : (Fin σ → ℤ) → (Fin σ → ℤ) → ℝ :=
  fun u v => φ (Fin.cons (ab.1 0) u) (Fin.cons (ab.2 0) v)

/-- The `σ`-fold cube term of the slices, as a family indexed by `z`. -/
def ctSlice {σ : ℕ} {Z : Type} (G : Z → ℤ → ℂ)
    (q : (Fin σ → ℤ) × (Fin σ → ℤ) × (Fin σ → ℤ)) : Z → ℤ → ℂ :=
  fun z y => Work.Peluse.cubeTerm q.2.1 q.2.2 (G z) y

/-- The column phase: the mixed phase of the row phase at the level-`σ` triple `q`. -/
def phCol {σ : ℕ} (φ : (Fin (σ+1) → ℤ) → (Fin (σ+1) → ℤ) → ℝ)
    (q : (Fin σ → ℤ) × (Fin σ → ℤ) × (Fin σ → ℤ)) : (Fin 1 → ℤ) → (Fin 1 → ℤ) → ℝ :=
  fun a b => Work.Peluse.Ulower.StepLe.mixedPhase
    (fun u v => φ (Fin.cons (a 0) u) (Fin.cons (b 0) v)) q

/-! ## Elementary analytic facts -/

/-- Iterated conjugation does not change the norm. -/
lemma norm_starIterate (n : ℕ) (z : ℂ) : ‖(star^[n]) z‖ = ‖z‖ := by
  induction n generalizing z with
  | zero => simp
  | succ k ih => rw [Function.iterate_succ_apply', norm_star, ih]

/-- The cube term of a `1`-bounded function is `1`-bounded. -/
lemma cubeTerm_norm_le_one {t : ℕ} (h h' : Fin t → ℤ) {f : ℤ → ℂ} (hf : ∀ x, ‖f x‖ ≤ 1)
    (x : ℤ) : ‖Work.Peluse.cubeTerm h h' f x‖ ≤ 1 := by
  rw [Work.Peluse.cubeTerm]
  calc ‖∏ ω : Fin t → Bool,
        (star^[Work.Peluse.weight ω]) (f (x + Work.Peluse.cornerShift h h' ω))‖
      = ∏ ω : Fin t → Bool,
        ‖(star^[Work.Peluse.weight ω]) (f (x + Work.Peluse.cornerShift h h' ω))‖ :=
        norm_prod _ _
    _ ≤ ∏ _ω : Fin t → Bool, (1 : ℝ) := by
        refine Finset.prod_le_prod₀ (fun ω _ => norm_nonneg _) (fun ω _ => ?_)
        rw [norm_starIterate]
        exact hf _
    _ = 1 := by simp

lemma hypoMass_nonneg {σ B : ℕ} {Z : Type} [Fintype Z] (G : Z → ℤ → ℂ)
    (H : Finset ((Fin σ → ℤ) × (Fin σ → ℤ)))
    (φ : (Fin σ → ℤ) → (Fin σ → ℤ) → ℝ) : 0 ≤ hypoMass σ B G H φ :=
  Finset.sum_nonneg (fun _ _ => pow_nonneg (norm_nonneg _) 2)

lemma concMass_nonneg {σ D B : ℕ} {Z : Type} [Fintype Z] (G : Z → ℤ → ℂ)
    (H : Finset ((Fin σ → ℤ) × (Fin σ → ℤ)))
    (φ : (Fin σ → ℤ) → (Fin σ → ℤ) → ℝ) : 0 ≤ concMass σ D B G H φ :=
  Finset.sum_nonneg (fun _ _ => pow_nonneg (norm_nonneg _) 2)

/-! ## Translated support at the enlarged scale -/

lemma mem_symIcc_iff {N : ℕ} {x : ℤ} : x ∈ Work.Peluse.symIcc N ↔ x.natAbs ≤ N := by
  rw [Work.Peluse.symIcc, Finset.mem_Icc]
  constructor
  · rintro ⟨h1, h2⟩
    have h3 : |x| ≤ (N : ℤ) := abs_le.mpr ⟨h1, h2⟩
    rw [Int.abs_eq_natAbs] at h3
    exact_mod_cast h3
  · intro h
    have h3 : ((x.natAbs : ℕ) : ℤ) ≤ (N : ℤ) := by exact_mod_cast h
    have h4 : |x| ≤ ((x.natAbs : ℕ) : ℤ) := le_of_eq (Int.abs_eq_natAbs x)
    exact abs_le.mp (le_trans h4 h3)

lemma notMem_symIcc_iff {N : ℕ} {x : ℤ} : x ∉ Work.Peluse.symIcc N ↔ N < x.natAbs := by
  simp only [mem_symIcc_iff, not_le]

lemma natAbs_le_of_mem_Icc_one {D : ℕ} {a : ℤ}
    (h : a ∈ Finset.Icc (1 : ℤ) (D : ℤ)) : a.natAbs ≤ D := by
  rw [Finset.mem_Icc] at h
  have h2 : |a| ≤ (D : ℤ) := abs_le.mpr ⟨by omega, h.2⟩
  rw [Int.abs_eq_natAbs] at h2
  exact_mod_cast h2

lemma cornerShift_natAbs_le {σ : ℕ} (h h' : Fin σ → ℤ) (ω : Fin σ → Bool) {D : ℕ}
    (hh : ∀ i, (h i).natAbs ≤ D) (hh' : ∀ i, (h' i).natAbs ≤ D) :
    (Work.Peluse.cornerShift h h' ω).natAbs ≤ σ * D := by
  rw [Work.Peluse.cornerShift]
  calc (∑ i : Fin σ, if ω i then h i else h' i).natAbs
      ≤ ∑ i : Fin σ, (if ω i then h i else h' i).natAbs := Int.natAbs_sum_le _ _
    _ ≤ ∑ _i : Fin σ, D := by
        refine Finset.sum_le_sum (fun i _ => ?_)
        by_cases hi : ω i <;> simp [hi, hh i, hh' i]
    _ = σ * D := by simp [Finset.sum_const, Finset.card_univ]

/-- The `σ`-fold cube term of a function supported (up to translation) in `symIcc L` is supported
(up to the same translation) in `symIcc (L + σ * D)`, provided the shifts are bounded by `D`. -/
lemma cubeTermSupport {σ L D : ℕ} (h h' : Fin σ → ℤ)
    (hh : ∀ i, (h i).natAbs ≤ D) (hh' : ∀ i, (h' i).natAbs ≤ D)
    {f : ℤ → ℂ} (c : ℤ) (hc : ∀ x, x ∉ Work.Peluse.symIcc L → f (x + c) = 0) :
    ∀ x, x ∉ Work.Peluse.symIcc (L + σ * D) → Work.Peluse.cubeTerm h h' f (x + c) = 0 := by
  intro x hx
  have hcs : (Work.Peluse.cornerShift h h' (fun _ : Fin σ => false)).natAbs ≤ σ * D :=
    cornerShift_natAbs_le h h' _ hh hh'
  have hxL : L + σ * D < x.natAbs := notMem_symIcc_iff.mp hx
  have hlt : L < (x + Work.Peluse.cornerShift h h' (fun _ : Fin σ => false)).natAbs := by
    have h2 : x.natAbs
        ≤ (x + Work.Peluse.cornerShift h h' (fun _ : Fin σ => false)).natAbs
          + (Work.Peluse.cornerShift h h' (fun _ : Fin σ => false)).natAbs := by
      have h3 := Int.natAbs_add_le
        (x + Work.Peluse.cornerShift h h' (fun _ : Fin σ => false))
        (-(Work.Peluse.cornerShift h h' (fun _ : Fin σ => false)))
      have h4 : x + Work.Peluse.cornerShift h h' (fun _ : Fin σ => false)
          + -(Work.Peluse.cornerShift h h' (fun _ : Fin σ => false)) = x := by ring
      rw [h4, Int.natAbs_neg] at h3
      exact h3
    omega
  have hz : f ((x + Work.Peluse.cornerShift h h' (fun _ : Fin σ => false)) + c) = 0 :=
    hc _ (notMem_symIcc_iff.mpr hlt)
  rw [Work.Peluse.cubeTerm]
  refine Finset.prod_eq_zero (Finset.mem_univ (fun _ : Fin σ => false)) ?_
  have hw : Work.Peluse.weight (fun _ : Fin σ => false) = 0 := by simp [Work.Peluse.weight]
  rw [hw, Function.iterate_zero_apply]
  have h5 : x + c + Work.Peluse.cornerShift h h' (fun _ : Fin σ => false)
      = (x + Work.Peluse.cornerShift h h' (fun _ : Fin σ => false)) + c := by ring
  rw [h5]
  exact hz

/-- The pair family `K^{(a,b)}_{(z,z')}(y) = G z (y+b) · conj (G z' (y+a))` of a
translate-supported family is translate-supported at the same scale. -/
lemma pairSupport {Z : Type} (G : Z → ℤ → ℂ) (L : ℕ)
    (hsupp : ∀ z, ∃ c₀ : ℤ, ∀ x : ℤ, x ∉ Work.Peluse.symIcc L → G z (x + c₀) = 0)
    (ab : (Fin 1 → ℤ) × (Fin 1 → ℤ)) (p : Z × Z) :
    ∃ c₀ : ℤ, ∀ x : ℤ, x ∉ Work.Peluse.symIcc L → Kp G ab p (x + c₀) = 0 := by
  obtain ⟨c, hc⟩ := hsupp p.1
  refine ⟨c - ab.2 0, fun x hx => ?_⟩
  show G p.1 ((x + (c - ab.2 0)) + ab.2 0) * star (G p.2 ((x + (c - ab.2 0)) + ab.1 0)) = 0
  have h1 : x + (c - ab.2 0) + ab.2 0 = x + c := by ring
  rw [h1, hc x hx, zero_mul]

/-! ## Averaging lemmas -/

/-- Conjugation commutes with a finite average. -/
lemma star_inv_card_sum {Z : Type} [Fintype Z] (F : Z → ℂ) :
    star (((Fintype.card Z : ℂ))⁻¹ * ∑ z, F z)
      = ((Fintype.card Z : ℂ))⁻¹ * ∑ z, star (F z) := by
  have hc : star (((Fintype.card Z : ℂ))⁻¹) = ((Fintype.card Z : ℂ))⁻¹ := by
    rw [Complex.star_def, map_inv₀, map_natCast]
  rw [star_mul, hc, star_sum, mul_comm]

/-- The average over `Z × Z` of a product of a function of the first and a function of the second
variable factorises. -/
lemma pair_sum_factor {Z : Type} [Fintype Z] (F G : Z → ℂ) :
    ((Fintype.card (Z × Z) : ℂ))⁻¹ * ∑ p : Z × Z, F p.1 * G p.2
      = (((Fintype.card Z : ℂ))⁻¹ * ∑ z, F z)
        * (((Fintype.card Z : ℂ))⁻¹ * ∑ z, G z) := by
  have hprod : ∑ p : Z × Z, F p.1 * G p.2 = (∑ z, F z) * (∑ z, G z) := by
    rw [Fintype.sum_prod_type]
    exact (Finset.sum_mul_sum Finset.univ Finset.univ F G).symm
  rw [hprod]
  have hcard : (Fintype.card (Z × Z) : ℂ)
      = (Fintype.card Z : ℂ) * (Fintype.card Z : ℂ) := by
    rw [Fintype.card_prod]; push_cast; ring
  rw [hcard, mul_inv_rev]
  ring

/-! ## The exponent arithmetic of the induction -/

/-- The exponent recurrence `d_{σ+1} = 4 (2^σ - 1) + 2 d_σ + 3σ + 1`, `d_σ = σ (2^{σ+1} - 3)`. -/
lemma ddExp_step (σ : ℕ) (hσ : 1 ≤ σ) :
    4 * (2 ^ σ - 1) + 2 * (σ * (2 ^ (σ + 1) - 3)) + (3 * σ + 1)
      = (σ + 1) * (2 ^ (σ + 2) - 3) := by
  apply Nat.cast_injective (R := ℤ)
  have hm : (2 : ℕ) ≤ 2 ^ σ := by
    calc (2 : ℕ) = 2 ^ 1 := by norm_num
      _ ≤ 2 ^ σ := Nat.pow_le_pow_right (by norm_num) hσ
  have h1 : 2 ^ (σ + 1) = 2 * 2 ^ σ := by rw [pow_succ]; ring
  have h2 : 2 ^ (σ + 2) = 4 * 2 ^ σ := by rw [show σ + 2 = σ + 1 + 1 by omega, pow_succ, h1]; ring
  have hle1 : (1 : ℕ) ≤ 2 ^ σ := le_trans (by norm_num) hm
  have hle2 : (3 : ℕ) ≤ 2 ^ (σ + 1) := by
    calc (3 : ℕ) ≤ 4 := by norm_num
      _ = 2 ^ 2 := by norm_num
      _ ≤ 2 ^ (σ + 1) := Nat.pow_le_pow_right (by norm_num) (by omega)
  have hle3 : (3 : ℕ) ≤ 2 ^ (σ + 2) := by
    calc (3 : ℕ) ≤ 4 := by norm_num
      _ = 2 ^ 2 := by norm_num
      _ ≤ 2 ^ (σ + 2) := Nat.pow_le_pow_right (by norm_num) (by omega)
  have c1 : (((2 ^ σ - 1 : ℕ)) : ℤ) = (2 ^ σ : ℤ) - 1 := Nat.cast_sub hle1
  have c2 : (((2 ^ (σ + 1) - 3 : ℕ)) : ℤ) = (2 ^ (σ + 1) : ℤ) - 3 := Nat.cast_sub hle2
  have c3 : (((2 ^ (σ + 2) - 3 : ℕ)) : ℤ) = (2 ^ (σ + 2) : ℤ) - 3 := Nat.cast_sub hle3
  have i1 : ((2 ^ (σ + 1) : ℕ) : ℤ) = 2 * ((2 ^ σ : ℕ) : ℤ) := by rw [h1]; push_cast; ring
  have i2 : ((2 ^ (σ + 2) : ℕ) : ℤ) = 4 * ((2 ^ σ : ℕ) : ℤ) := by rw [h2]; push_cast; ring
  simp only [Nat.cast_add, Nat.cast_mul, Nat.cast_one, Nat.cast_ofNat, c1, c2, c3, i1, i2]
  ring

/-! ## The three delegated combinatorial ingredients (statements fixed by their own files) -/

lemma thetaFan_aux {σ D : ℕ}
    (H : Finset ((Fin (σ+1) → ℤ) × (Fin (σ+1) → ℤ)))
    {M : Type*} [AddCommMonoid M]
    (f : (Fin (σ+1) → ℤ) × (Fin (σ+1) → ℤ) × (Fin (σ+1) → ℤ) → M) :
    (∑ k ∈ Work.Peluse.Ulower.ThetaSet (σ+1) D H, f k)
      = ∑ k' ∈ (Work.Peluse.Ulower.thetaBox σ D ×ˢ (Work.Peluse.Ulower.thetaBox σ D ×ˢ
              Work.Peluse.Ulower.thetaBox σ D)),
          ∑ k'' ∈ Work.Peluse.Ulower.ThetaSet 1 D
              (Work.Peluse.Ulower.StepLe.colFibre σ D H k'),
            f (Fin.cons (k''.1 0) k'.1, Fin.cons (k''.2.1 0) k'.2.1,
               Fin.cons (k''.2.2 0) k'.2.2) :=
  Work.Peluse.Ulower.StepLe.sharpStep.thetaFan H f

lemma rowColTranspose_aux {σ D : ℕ}
    (H : Finset ((Fin (σ+1) → ℤ) × (Fin (σ+1) → ℤ)))
    {M : Type*} [AddCommMonoid M]
    (f : ((Fin 1 → ℤ) × (Fin 1 → ℤ)) ×
          ((Fin σ → ℤ) × (Fin σ → ℤ) × (Fin σ → ℤ)) → M) :
    (∑ ab ∈ (Work.Peluse.Ulower.thetaBox 1 D ×ˢ Work.Peluse.Ulower.thetaBox 1 D),
        ∑ q ∈ Work.Peluse.Ulower.ThetaSet σ D
              (Work.Peluse.Ulower.StepLe.rowFibre σ D H (ab.1 0) (ab.2 0)), f (ab, q))
      = ∑ q ∈ (Work.Peluse.Ulower.thetaBox σ D ×ˢ (Work.Peluse.Ulower.thetaBox σ D ×ˢ
              Work.Peluse.Ulower.thetaBox σ D)),
          ∑ ab ∈ Work.Peluse.Ulower.StepLe.colFibre σ D H q, f (ab, q) :=
  Work.Peluse.Ulower.StepLe.sharpStep.rowCol_transpose H f

lemma hypoMassRow_aux {σ D B : ℕ} {Z : Type} [Fintype Z] (G : Z → ℤ → ℂ)
    (H : Finset ((Fin (σ+1) → ℤ) × (Fin (σ+1) → ℤ)))
    (φ : (Fin (σ+1) → ℤ) → (Fin (σ+1) → ℤ) → ℝ)
    (hcoords : ∀ p ∈ H, ∀ i : Fin (σ+1),
      p.1 i ∈ Finset.Icc (1:ℤ) (D:ℤ) ∧ p.2 i ∈ Finset.Icc (1:ℤ) (D:ℤ)) :
    Work.Peluse.Ulower.StepLe.hypoMass (σ+1) B G H φ
      = ∑ ab ∈ (Work.Peluse.Ulower.thetaBox 1 D ×ˢ Work.Peluse.Ulower.thetaBox 1 D),
          Work.Peluse.Ulower.StepLe.hypoMass σ B
            (fun p : Z × Z => fun y => G p.1 (y + ab.2 0) * star (G p.2 (y + ab.1 0)))
            (Work.Peluse.Ulower.StepLe.rowFibre σ D H (ab.1 0) (ab.2 0))
            (fun u v => φ (Fin.cons (ab.1 0) u) (Fin.cons (ab.2 0) v)) :=
  Work.Peluse.Ulower.StepLe.sharpStep.hypoMass_succ_row G H φ hcoords

/-! ## The two pointwise object identities -/

/-- The row object (level `σ` cube term of the pair family) equals the column object (level-`1`
cube term of the average of the slices). -/
lemma rowObj_eq_colObj {σ : ℕ} {Z : Type} [Fintype Z] (G : Z → ℤ → ℂ)
    (ab : (Fin 1 → ℤ) × (Fin 1 → ℤ))
    (q : (Fin σ → ℤ) × (Fin σ → ℤ) × (Fin σ → ℤ)) (x : ℤ) :
    ((Fintype.card (Z × Z) : ℂ))⁻¹ * ∑ p : Z × Z,
        Work.Peluse.cubeTerm q.2.1 q.2.2 (Kp G ab p) x
      = Work.Peluse.cubeTerm ab.1 ab.2 (fun y => ((Fintype.card Z : ℂ))⁻¹ *
          ∑ z, Work.Peluse.cubeTerm q.2.1 q.2.2 (G z) y) x := by
  have hsum : ∑ p : Z × Z, Work.Peluse.cubeTerm q.2.1 q.2.2 (Kp G ab p) x
      = ∑ p : Z × Z, (Work.Peluse.cubeTerm q.2.1 q.2.2 (G p.1) (x + ab.2 0)
          * star (Work.Peluse.cubeTerm q.2.1 q.2.2 (G p.2) (x + ab.1 0))) := by
    refine Finset.sum_congr rfl (fun p _ => ?_)
    have heq : Kp G ab p = (fun y => G p.1 (y + ab.2 0) * star (G p.2 (y + ab.1 0))) := rfl
    rw [heq]
    exact Work.Peluse.Ulower.StepLe.ddiSharp.cubeTerm_mul_shift (h := q.2.1) (h' := q.2.2)
      (f := G p.1) (g := G p.2) (c := ab.2 0) (d := ab.1 0) (x := x)
  rw [hsum]
  rw [pair_sum_factor (fun z : Z => Work.Peluse.cubeTerm q.2.1 q.2.2 (G z) (x + ab.2 0))
        (fun z : Z => star (Work.Peluse.cubeTerm q.2.1 q.2.2 (G z) (x + ab.1 0)))]
  conv_rhs => rw [Work.Peluse.Ulower.StepLe.ddiSharp.one.cubeTerm_fin1, star_inv_card_sum]

/-- The level-`1` cube term of the `σ`-fold cube term of the slices is the level-`(σ+1)` cube term
of the slices (the column form of the cube-term peel). -/
lemma ctSlice_eq {σ : ℕ} {Z : Type} (G : Z → ℤ → ℂ)
    (q : (Fin σ → ℤ) × (Fin σ → ℤ) × (Fin σ → ℤ))
    (k'' : (Fin 1 → ℤ) × (Fin 1 → ℤ) × (Fin 1 → ℤ)) (z : Z) (x : ℤ) :
    Work.Peluse.cubeTerm k''.2.1 k''.2.2 (ctSlice G q z) x
      = Work.Peluse.cubeTerm (Fin.cons (k''.2.1 0) q.2.1) (Fin.cons (k''.2.2 0) q.2.2)
          (G z) x := by
  have h := Work.Peluse.Ulower.StepLe.ddiSharp.cubeTerm_cons_one (σ := σ)
      (k''.2.1 0) (k''.2.2 0) q.2.1 q.2.2 (G z) x
  rw [h]
  rw [show k''.2.1 = (fun _ : Fin 1 => k''.2.1 0) from
        funext (fun i => congrArg k''.2.1 (Subsingleton.elim i 0)),
      show k''.2.2 = (fun _ : Fin 1 => k''.2.2 0) from
        funext (fun i => congrArg k''.2.2 (Subsingleton.elim i 0))]
  rfl

/-- The row phase and the column phase agree: `mixedPhase (φ_ab) q = φ̄_ab`. -/
lemma mixedPhase_phRow_phCol {σ : ℕ} (φ : (Fin (σ+1) → ℤ) → (Fin (σ+1) → ℤ) → ℝ)
    (ab : (Fin 1 → ℤ) × (Fin 1 → ℤ))
    (q : (Fin σ → ℤ) × (Fin σ → ℤ) × (Fin σ → ℤ)) :
    mixedPhase (phRow φ ab) q = phCol φ q ab.1 ab.2 := rfl

/-- Splitting the mixed phase of the `(σ+1)`-fold phase at the first coordinate gives the mixed
phase of the column phase. -/
lemma mixedPhase_cons_eq_phCol {σ : ℕ} (φ : (Fin (σ+1) → ℤ) → (Fin (σ+1) → ℤ) → ℝ)
    (q : (Fin σ → ℤ) × (Fin σ → ℤ) × (Fin σ → ℤ))
    (k'' : (Fin 1 → ℤ) × (Fin 1 → ℤ) × (Fin 1 → ℤ)) :
    mixedPhase φ (Fin.cons (k''.1 0) q.1, Fin.cons (k''.2.1 0) q.2.1,
        Fin.cons (k''.2.2 0) q.2.2)
      = mixedPhase (phCol φ q) k'' := by
  rw [Work.Peluse.Ulower.StepLe.ddiSharp.mixedPhase_cons,
    Work.Peluse.Ulower.StepLe.ddiSharp.one.mixedPhase_fin1]
  rfl

/-! ## The two transpositions -/

/-- **Transposition I.**  Summing the conclusion mass over the rows `(a,b)` and swapping the order
of summation over the incidence `q ∈ Θ_σ(rowFibre H (a,b))` turns it into the sum over the
σ-triples `q` of the hypothesis mass of the level-`1` instance for the slice family
`z ↦ ct(q)(G z)`. -/
lemma concMass_row_sum_eq_colMass {σ D B : ℕ} {Z : Type} [Fintype Z] (G : Z → ℤ → ℂ)
    (H : Finset ((Fin (σ+1) → ℤ) × (Fin (σ+1) → ℤ)))
    (φ : (Fin (σ+1) → ℤ) → (Fin (σ+1) → ℤ) → ℝ) :
    (∑ ab ∈ (Work.Peluse.Ulower.thetaBox 1 D ×ˢ Work.Peluse.Ulower.thetaBox 1 D),
        concMass σ D B (Kp G ab) (rowFibre σ D H (ab.1 0) (ab.2 0)) (phRow φ ab))
      = ∑ q ∈ (Work.Peluse.Ulower.thetaBox σ D ×ˢ (Work.Peluse.Ulower.thetaBox σ D ×ˢ
            Work.Peluse.Ulower.thetaBox σ D)),
          hypoMass 1 B (ctSlice G q) (colFibre σ D H q) (phCol φ q) := by
  have hL : ∀ ab ∈ (Work.Peluse.Ulower.thetaBox 1 D ×ˢ Work.Peluse.Ulower.thetaBox 1 D),
      concMass σ D B (Kp G ab) (rowFibre σ D H (ab.1 0) (ab.2 0)) (phRow φ ab)
        = ∑ q ∈ Work.Peluse.Ulower.ThetaSet σ D (rowFibre σ D H (ab.1 0) (ab.2 0)),
            ‖((B : ℂ))⁻¹ * ∑' x : ℤ, ((Fintype.card (Z × Z) : ℂ))⁻¹ *
              ∑ p : Z × Z, Work.Peluse.cubeTerm q.2.1 q.2.2 (Kp G ab p) x *
              Complex.exp (2 * Real.pi * Complex.I *
                ((mixedPhase (phRow φ ab) q : ℝ) : ℂ) * (x : ℂ))‖ ^ 2 := by
    intro ab _
    rw [concMass]
  have hR : ∀ q ∈ (Work.Peluse.Ulower.thetaBox σ D ×ˢ (Work.Peluse.Ulower.thetaBox σ D ×ˢ
        Work.Peluse.Ulower.thetaBox σ D)),
      hypoMass 1 B (ctSlice G q) (colFibre σ D H q) (phCol φ q)
        = ∑ ab ∈ colFibre σ D H q,
            ‖((B : ℂ))⁻¹ * ∑' x : ℤ, ((Fintype.card (Z × Z) : ℂ))⁻¹ *
              ∑ p : Z × Z, Work.Peluse.cubeTerm q.2.1 q.2.2 (Kp G ab p) x *
              Complex.exp (2 * Real.pi * Complex.I *
                ((mixedPhase (phRow φ ab) q : ℝ) : ℂ) * (x : ℂ))‖ ^ 2 := by
    intro q _
    rw [hypoMass]
    refine Finset.sum_congr rfl (fun ab _ => ?_)
    refine congrArg (fun t : ℂ => ‖((B : ℂ))⁻¹ * t‖ ^ 2) ?_
    refine tsum_congr (fun x : ℤ => ?_)
    rw [mixedPhase_phRow_phCol φ ab q]
    rw [← Finset.sum_mul, ← mul_assoc]
    rw [rowObj_eq_colObj G ab q x]
    rfl
  rw [Finset.sum_congr rfl hL]
  rw [rowColTranspose_aux H (fun pq =>
    ‖((B : ℂ))⁻¹ * ∑' x : ℤ, ((Fintype.card (Z × Z) : ℂ))⁻¹ *
      ∑ p : Z × Z, Work.Peluse.cubeTerm pq.2.2.1 pq.2.2.2 (Kp G pq.1 p) x *
      Complex.exp (2 * Real.pi * Complex.I *
        ((mixedPhase (phRow φ pq.1) pq.2 : ℝ) : ℂ) * (x : ℂ))‖ ^ 2)]
  rw [← Finset.sum_congr rfl hR]

/-- **Transposition II.**  Summing the conclusion mass over the σ-triples `q` and expanding
`Θ_{σ+1}(H)` at the first coordinate turns it into the conclusion mass at level `σ+1`. -/
lemma colMass_sum_eq_concMass {σ D B : ℕ} {Z : Type} [Fintype Z] (G : Z → ℤ → ℂ)
    (H : Finset ((Fin (σ+1) → ℤ) × (Fin (σ+1) → ℤ)))
    (φ : (Fin (σ+1) → ℤ) → (Fin (σ+1) → ℤ) → ℝ) :
    (∑ q ∈ (Work.Peluse.Ulower.thetaBox σ D ×ˢ (Work.Peluse.Ulower.thetaBox σ D ×ˢ
          Work.Peluse.Ulower.thetaBox σ D)),
        concMass 1 D B (ctSlice G q) (colFibre σ D H q) (phCol φ q))
      = concMass (σ+1) D B G H φ := by
  rw [concMass]
  rw [thetaFan_aux H (f := fun k => ‖((B : ℂ))⁻¹ * ∑' x : ℤ,
        ((Fintype.card Z : ℂ))⁻¹ * ∑ z : Z, Work.Peluse.cubeTerm k.2.1 k.2.2 (G z) x *
        Complex.exp (2 * Real.pi * Complex.I * ((mixedPhase φ k : ℝ) : ℂ) * (x : ℂ))‖ ^ 2)]
  refine Finset.sum_congr rfl (fun q _ => ?_)
  rw [concMass]
  refine Finset.sum_congr rfl (fun k'' _ => ?_)
  refine congrArg (fun t : ℂ => ‖((B : ℂ))⁻¹ * t‖ ^ 2) ?_
  refine tsum_congr (fun x : ℤ => ?_)
  congr 1
  refine Finset.sum_congr rfl (fun z _ => ?_)
  rw [mixedPhase_cons_eq_phCol φ q k'', ctSlice_eq G q k'' z x]

/-- Collecting the `D`-powers of the final estimate. -/
lemma dpow_collect (x : ℝ) (a b c : ℕ) (C2 C3 R : ℝ) :
    x ^ a * (C2 * x ^ b * (x ^ c * (C3 * x * R))) = C2 * C3 * x ^ (a + b + c + 1) * R := by
  have h : x ^ a * (C2 * x ^ b * (x ^ c * (C3 * x * R)))
      = C2 * C3 * (((x ^ a * x ^ b) * x ^ c) * x) * R := by ring
  rw [h, ← pow_add, ← pow_add, ← pow_succ]

theorem sharpMassDDI_step {σ : ℕ} (hσ : 1 ≤ σ)
    (IH : Work.Peluse.Ulower.StepLe.SharpMassDDI σ)
    (IH1 : Work.Peluse.Ulower.StepLe.SharpMassDDI 1) :
    Work.Peluse.Ulower.StepLe.SharpMassDDI (σ + 1) := by
  obtain ⟨C, hCpos, hC⟩ := IH
  obtain ⟨C1, hC1pos, hC1⟩ := IH1
  refine ⟨C ^ 2 * C1, mul_pos (pow_pos hCpos 2) hC1pos, ?_⟩
  intro L D B hL hD hB Z _ G hG1 hGsup H φ hH
  have hDpos : (0 : ℝ) < (D : ℝ) := by exact_mod_cast (show 0 < D by omega)
  set S₁ : Finset ((Fin 1 → ℤ) × (Fin 1 → ℤ)) :=
    Work.Peluse.Ulower.thetaBox 1 D ×ˢ Work.Peluse.Ulower.thetaBox 1 D with hS₁
  set S₂ : Finset ((Fin σ → ℤ) × (Fin σ → ℤ) × (Fin σ → ℤ)) :=
    Work.Peluse.Ulower.thetaBox σ D ×ˢ (Work.Peluse.Ulower.thetaBox σ D ×ˢ
      Work.Peluse.Ulower.thetaBox σ D) with hS₂
  set A : (Fin 1 → ℤ) × (Fin 1 → ℤ) → ℝ := fun ab =>
    hypoMass σ B (Kp G ab) (rowFibre σ D H (ab.1 0) (ab.2 0)) (phRow φ ab) with hA
  set cM : (Fin 1 → ℤ) × (Fin 1 → ℤ) → ℝ := fun ab =>
    concMass σ D B (Kp G ab) (rowFibre σ D H (ab.1 0) (ab.2 0)) (phRow φ ab) with hcM
  set H2 : (Fin σ → ℤ) × (Fin σ → ℤ) × (Fin σ → ℤ) → ℝ := fun q =>
    hypoMass 1 B (ctSlice G q) (colFibre σ D H q) (phCol φ q) with hH2
  set cC : (Fin σ → ℤ) × (Fin σ → ℤ) × (Fin σ → ℤ) → ℝ := fun q =>
    concMass 1 D B (ctSlice G q) (colFibre σ D H q) (phCol φ q) with hcC
  have hA0 : ∀ ab : (Fin 1 → ℤ) × (Fin 1 → ℤ), 0 ≤ A ab := by
    intro ab
    simp only [hA]
    exact hypoMass_nonneg _ _ _
  -- (i) the row decomposition of the hypothesis mass
  have hrow : hypoMass (σ+1) B G H φ = ∑ ab ∈ S₁, A ab := by
    simp only [hA, hS₁]
    exact hypoMassRow_aux G H φ hH
  -- (ii) the induction hypothesis, row by row
  have hIH : ∀ ab ∈ S₁, (A ab) ^ (2 ^ σ)
      ≤ C * (D : ℝ) ^ (σ * (2 ^ (σ + 1) - 3)) * cM ab := by
    intro ab _
    have hB' : L + σ * D ≤ B := by
      have h : σ * D ≤ (σ + 1) * D := by
        rw [Nat.succ_mul]
        exact Nat.le_add_right _ _
      omega
    have hbound : ∀ p : Z × Z, ∀ x : ℤ, ‖Kp G ab p x‖ ≤ 1 := by
      intro p x
      have heq : Kp G ab p
          = (fun y => G p.1 (y + ab.2 0) * star (G p.2 (y + ab.1 0))) := rfl
      rw [heq, norm_mul, norm_star]
      exact mul_le_one₀ (hG1 p.1 _) (norm_nonneg _) (hG1 p.2 _)
    have hsupp : ∀ p : Z × Z, ∃ c₀ : ℤ, ∀ x : ℤ,
        x ∉ Work.Peluse.symIcc L → Kp G ab p (x + c₀) = 0 :=
      fun p => pairSupport G L hGsup ab p
    have hcoord : ∀ p ∈ rowFibre σ D H (ab.1 0) (ab.2 0), ∀ i : Fin σ,
        p.1 i ∈ Finset.Icc (1 : ℤ) (D : ℤ) ∧ p.2 i ∈ Finset.Icc (1 : ℤ) (D : ℤ) := by
      intro p hp i
      have hp2 : p ∈ Work.Peluse.Ulower.thetaBox σ D ×ˢ Work.Peluse.Ulower.thetaBox σ D := by
        rw [rowFibre] at hp
        exact (Finset.mem_filter.mp hp).1
      exact ⟨Work.Peluse.Ulower.mem_thetaBox.mp (Finset.mem_product.mp hp2).1 i,
             Work.Peluse.Ulower.mem_thetaBox.mp (Finset.mem_product.mp hp2).2 i⟩
    have hres := hC hL hD hB' (Kp G ab) hbound hsupp
        (rowFibre σ D H (ab.1 0) (ab.2 0)) (phRow φ ab) hcoord
    simp only [hA, hcM]
    have hDp : (0 : ℝ) < (D : ℝ) ^ (σ * (2 ^ (σ + 1) - 3)) := pow_pos hDpos _
    rw [div_le_iff₀ hDp] at hres
    calc (hypoMass σ B (Kp G ab) (rowFibre σ D H (ab.1 0) (ab.2 0)) (phRow φ ab)) ^ (2 ^ σ)
        = C * (C⁻¹ * (hypoMass σ B (Kp G ab) (rowFibre σ D H (ab.1 0) (ab.2 0))
              (phRow φ ab)) ^ (2 ^ σ)) := by
          rw [← mul_assoc, mul_inv_cancel₀ (ne_of_gt hCpos), one_mul]
      _ ≤ C * (concMass σ D B (Kp G ab) (rowFibre σ D H (ab.1 0) (ab.2 0)) (phRow φ ab)
              * (D : ℝ) ^ (σ * (2 ^ (σ + 1) - 3))) :=
          mul_le_mul_of_nonneg_left hres (le_of_lt hCpos)
      _ = C * (D : ℝ) ^ (σ * (2 ^ (σ + 1) - 3))
            * concMass σ D B (Kp G ab) (rowFibre σ D H (ab.1 0) (ab.2 0)) (phRow φ ab) := by
          ring
  -- (iii) the level-one induction hypothesis, triple by triple
  have hIH1 : ∀ q ∈ S₂, (H2 q) ^ 2 ≤ C1 * (D : ℝ) * cC q := by
    intro q hq
    have hq' : q ∈ Work.Peluse.Ulower.thetaBox σ D ×ˢ (Work.Peluse.Ulower.thetaBox σ D ×ˢ
        Work.Peluse.Ulower.thetaBox σ D) := by rwa [hS₂] at hq
    have hq21 : q.2.1 ∈ Work.Peluse.Ulower.thetaBox σ D :=
      (Finset.mem_product.mp (Finset.mem_product.mp hq').2).1
    have hq22 : q.2.2 ∈ Work.Peluse.Ulower.thetaBox σ D :=
      (Finset.mem_product.mp (Finset.mem_product.mp hq').2).2
    have hq1 : ∀ i : Fin σ, (q.2.1 i).natAbs ≤ D := fun i =>
      natAbs_le_of_mem_Icc_one (Work.Peluse.Ulower.mem_thetaBox.mp hq21 i)
    have hq2 : ∀ i : Fin σ, (q.2.2 i).natAbs ≤ D := fun i =>
      natAbs_le_of_mem_Icc_one (Work.Peluse.Ulower.mem_thetaBox.mp hq22 i)
    have hB' : L + σ * D + 1 * D ≤ B := by
      have h : L + (σ + 1) * D = L + σ * D + 1 * D := by
        rw [Nat.succ_mul, Nat.one_mul, Nat.add_assoc]
      omega
    have hL' : 1 ≤ L + σ * D := le_trans hL (Nat.le_add_right _ _)
    have hbound : ∀ z : Z, ∀ x : ℤ, ‖ctSlice G q z x‖ ≤ 1 :=
      fun z x => cubeTerm_norm_le_one q.2.1 q.2.2 (hG1 z) x
    have hsupp : ∀ z : Z, ∃ c₀ : ℤ, ∀ x : ℤ,
        x ∉ Work.Peluse.symIcc (L + σ * D) → ctSlice G q z (x + c₀) = 0 := by
      intro z
      obtain ⟨c, hc⟩ := hGsup z
      exact ⟨c, fun x hx => cubeTermSupport q.2.1 q.2.2 hq1 hq2 c hc x hx⟩
    have hcoord : ∀ ab ∈ colFibre σ D H q, ∀ i : Fin 1,
        ab.1 i ∈ Finset.Icc (1 : ℤ) (D : ℤ) ∧ ab.2 i ∈ Finset.Icc (1 : ℤ) (D : ℤ) := by
      intro ab hab i
      have hab2 : ab ∈ Work.Peluse.Ulower.thetaBox 1 D ×ˢ Work.Peluse.Ulower.thetaBox 1 D := by
        rw [colFibre] at hab
        exact (Finset.mem_filter.mp hab).1
      exact ⟨Work.Peluse.Ulower.mem_thetaBox.mp (Finset.mem_product.mp hab2).1 i,
             Work.Peluse.Ulower.mem_thetaBox.mp (Finset.mem_product.mp hab2).2 i⟩
    have hres := hC1 hL' hD hB' (ctSlice G q) hbound hsupp (colFibre σ D H q) (phCol φ q)
      hcoord
    simp only [hH2, hcC]
    have h21 : ((2 : ℕ) ^ 1) = 2 := by norm_num
    have hDexp : (1 * (2 ^ (1 + 1) - 3) : ℕ) = 1 := by norm_num
    rw [h21, hDexp, pow_one] at hres
    rw [div_le_iff₀ hDpos] at hres
    calc (hypoMass 1 B (ctSlice G q) (colFibre σ D H q) (phCol φ q)) ^ 2
        = C1 * (C1⁻¹ * (hypoMass 1 B (ctSlice G q) (colFibre σ D H q) (phCol φ q)) ^ 2) := by
          rw [← mul_assoc, mul_inv_cancel₀ (ne_of_gt hC1pos), one_mul]
      _ ≤ C1 * (concMass 1 D B (ctSlice G q) (colFibre σ D H q) (phCol φ q) * (D : ℝ)) :=
          mul_le_mul_of_nonneg_left hres (le_of_lt hC1pos)
      _ = C1 * (D : ℝ) * concMass 1 D B (ctSlice G q) (colFibre σ D H q) (phCol φ q) := by ring
  -- (iv) the two transpositions
  have htr1 : (∑ ab ∈ S₁, cM ab) = ∑ q ∈ S₂, H2 q := by
    simp only [hcM, hH2, hS₁, hS₂]
    exact concMass_row_sum_eq_colMass G H φ
  have htr2 : (∑ q ∈ S₂, cC q) = concMass (σ+1) D B G H φ := by
    simp only [hcC, hS₂]
    exact colMass_sum_eq_concMass G H φ
  -- (v) the cardinalities of the row and triple boxes
  have hcard1 : ((S₁.card : ℕ) : ℝ) = (D : ℝ) ^ 2 := by
    rw [hS₁, Finset.card_product, Work.Peluse.Ulower.thetaBox_card, pow_one, Nat.cast_mul]
    ring
  have hcard2 : ((S₂.card : ℕ) : ℝ) = (D : ℝ) ^ (3 * σ) := by
    rw [hS₂, Finset.card_product, Finset.card_product, Work.Peluse.Ulower.thetaBox_card]
    simp only [Nat.cast_mul, Nat.cast_pow]
    rw [← pow_add, ← pow_add]
    congr 1
    ring
  -- (vi) the power mean and Cauchy--Schwarz steps
  have step1 : (hypoMass (σ+1) B G H φ) ^ (2 ^ (σ + 1))
      ≤ (D : ℝ) ^ (4 * (2 ^ σ - 1)) * (∑ ab ∈ S₁, (A ab) ^ (2 ^ σ)) ^ 2 := by
    rw [hrow]
    rw [show 2 ^ (σ + 1) = 2 ^ σ * 2 by rw [pow_succ]]
    rw [pow_mul]
    have hpm := pow_sum_le_card_mul_sum_pow (s := S₁) (f := fun ab => A ab)
      (fun i _ => hA0 i) (2 ^ σ - 1)
    rw [Nat.sub_add_cancel Nat.one_le_two_pow] at hpm
    rw [hcard1] at hpm
    calc ((∑ ab ∈ S₁, A ab) ^ (2 ^ σ)) ^ 2
        ≤ (((D : ℝ) ^ 2) ^ (2 ^ σ - 1) * ∑ ab ∈ S₁, (A ab) ^ (2 ^ σ)) ^ 2 :=
          pow_le_pow_left₀ (pow_nonneg (Finset.sum_nonneg (fun ab _ => hA0 ab)) _) hpm 2
      _ = ((D : ℝ) ^ 2) ^ ((2 ^ σ - 1) * 2) * (∑ ab ∈ S₁, (A ab) ^ (2 ^ σ)) ^ 2 := by
          rw [mul_pow, pow_mul]
      _ = (D : ℝ) ^ (4 * (2 ^ σ - 1)) * (∑ ab ∈ S₁, (A ab) ^ (2 ^ σ)) ^ 2 := by
          rw [show ((D : ℝ) ^ 2) ^ ((2 ^ σ - 1) * 2) = (D : ℝ) ^ (4 * (2 ^ σ - 1)) by
            rw [← pow_mul]; congr 1; ring]
  have step2 : (∑ ab ∈ S₁, (A ab) ^ (2 ^ σ)) ^ 2
      ≤ (C * (D : ℝ) ^ (σ * (2 ^ (σ + 1) - 3))) ^ 2 * (∑ ab ∈ S₁, cM ab) ^ 2 := by
    have h4 : ∑ ab ∈ S₁, (A ab) ^ (2 ^ σ)
        ≤ C * (D : ℝ) ^ (σ * (2 ^ (σ + 1) - 3)) * ∑ ab ∈ S₁, cM ab := by
      calc ∑ ab ∈ S₁, (A ab) ^ (2 ^ σ)
          ≤ ∑ ab ∈ S₁, C * (D : ℝ) ^ (σ * (2 ^ (σ + 1) - 3)) * cM ab :=
            Finset.sum_le_sum hIH
        _ = C * (D : ℝ) ^ (σ * (2 ^ (σ + 1) - 3)) * ∑ ab ∈ S₁, cM ab := by
            rw [Finset.mul_sum]
    calc (∑ ab ∈ S₁, (A ab) ^ (2 ^ σ)) ^ 2
        ≤ (C * (D : ℝ) ^ (σ * (2 ^ (σ + 1) - 3)) * ∑ ab ∈ S₁, cM ab) ^ 2 :=
          pow_le_pow_left₀ (Finset.sum_nonneg (fun ab _ => pow_nonneg (hA0 ab) _)) h4 2
      _ = (C * (D : ℝ) ^ (σ * (2 ^ (σ + 1) - 3))) ^ 2 * (∑ ab ∈ S₁, cM ab) ^ 2 := by
          rw [mul_pow]
  have step3 : (∑ q ∈ S₂, H2 q) ^ 2 ≤ (D : ℝ) ^ (3 * σ) * ∑ q ∈ S₂, (H2 q) ^ 2 := by
    have hcs := sq_sum_le_card_mul_sum_sq (s := S₂) (f := fun q => H2 q)
    rw [hcard2] at hcs
    exact hcs
  have step4 : ∑ q ∈ S₂, (H2 q) ^ 2 ≤ C1 * (D : ℝ) * ∑ q ∈ S₂, cC q := by
    calc ∑ q ∈ S₂, (H2 q) ^ 2 ≤ ∑ q ∈ S₂, C1 * (D : ℝ) * cC q := Finset.sum_le_sum hIH1
      _ = C1 * (D : ℝ) * ∑ q ∈ S₂, cC q := by rw [Finset.mul_sum]
  -- (vii) the combination
  have hQ : (∑ ab ∈ S₁, cM ab) ^ 2
      ≤ (D : ℝ) ^ (3 * σ) * (C1 * (D : ℝ) * concMass (σ+1) D B G H φ) := by
    rw [htr1]
    calc (∑ q ∈ S₂, H2 q) ^ 2 ≤ (D : ℝ) ^ (3 * σ) * ∑ q ∈ S₂, (H2 q) ^ 2 := step3
      _ ≤ (D : ℝ) ^ (3 * σ) * (C1 * (D : ℝ) * ∑ q ∈ S₂, cC q) :=
          mul_le_mul_of_nonneg_left step4 (pow_nonneg (le_of_lt hDpos) _)
      _ = (D : ℝ) ^ (3 * σ) * (C1 * (D : ℝ) * concMass (σ+1) D B G H φ) := by rw [htr2]
  have hstep : (hypoMass (σ+1) B G H φ) ^ (2 ^ (σ + 1))
      ≤ (C ^ 2 * C1) * (D : ℝ) ^ ((σ + 1) * (2 ^ (σ + 2) - 3))
          * concMass (σ+1) D B G H φ := by
    calc (hypoMass (σ+1) B G H φ) ^ (2 ^ (σ + 1))
        ≤ (D : ℝ) ^ (4 * (2 ^ σ - 1)) * (∑ ab ∈ S₁, (A ab) ^ (2 ^ σ)) ^ 2 := step1
      _ ≤ (D : ℝ) ^ (4 * (2 ^ σ - 1))
            * ((C * (D : ℝ) ^ (σ * (2 ^ (σ + 1) - 3))) ^ 2 * (∑ ab ∈ S₁, cM ab) ^ 2) :=
          mul_le_mul_of_nonneg_left step2 (pow_nonneg (le_of_lt hDpos) _)
      _ ≤ (D : ℝ) ^ (4 * (2 ^ σ - 1))
            * ((C * (D : ℝ) ^ (σ * (2 ^ (σ + 1) - 3))) ^ 2
              * ((D : ℝ) ^ (3 * σ) * (C1 * (D : ℝ) * concMass (σ+1) D B G H φ))) :=
          mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hQ (by positivity))
            (pow_nonneg (le_of_lt hDpos) _)
      _ = (C ^ 2 * C1) * (D : ℝ) ^ ((σ + 1) * (2 ^ (σ + 2) - 3))
            * concMass (σ+1) D B G H φ := by
          rw [mul_pow]
          have hp1 : ((D : ℝ) ^ (σ * (2 ^ (σ + 1) - 3))) ^ 2
              = (D : ℝ) ^ (2 * (σ * (2 ^ (σ + 1) - 3))) := by
            rw [← pow_mul]; congr 1; ring
          rw [hp1]
          rw [dpow_collect (D : ℝ) (4 * (2 ^ σ - 1)) (2 * (σ * (2 ^ (σ + 1) - 3))) (3 * σ)
            (C ^ 2) C1 (concMass (σ+1) D B G H φ)]
          rw [Nat.add_assoc, ddExp_step σ hσ]
  -- (viii) divide out the constant and the `D`-power
  have hC' : (0 : ℝ) < C ^ 2 * C1 := mul_pos (pow_pos hCpos 2) hC1pos
  have hD' : (0 : ℝ) < (D : ℝ) ^ ((σ + 1) * (2 ^ (σ + 2) - 3)) := pow_pos hDpos _
  rw [div_le_iff₀ hD']
  calc (C ^ 2 * C1)⁻¹ * (hypoMass (σ+1) B G H φ) ^ (2 ^ (σ + 1))
      ≤ (C ^ 2 * C1)⁻¹ * ((C ^ 2 * C1) * (D : ℝ) ^ ((σ + 1) * (2 ^ (σ + 2) - 3))
          * concMass (σ+1) D B G H φ) :=
        mul_le_mul_of_nonneg_left hstep (by positivity)
    _ = concMass (σ+1) D B G H φ * (D : ℝ) ^ ((σ + 1) * (2 ^ (σ + 2) - 3)) := by
        rw [← mul_assoc, ← mul_assoc, inv_mul_cancel₀ (ne_of_gt hC'), one_mul]
        ring

end Work.Peluse.Ulower.StepLe
