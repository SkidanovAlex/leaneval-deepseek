import Mathlib
import Submission.Work.EQ.CycleDefs
import Submission.Work.EQ.H0_invParam_ge
import Submission.Work.EQ.component_shiftZ_invariant
import Submission.Work.EQ.exists_finset_zpow_annulus

/-! # The annulus-to-`ℂ*` transport for `CompactModPunctures`

If a `σ`-invariant set `S ⊆ ⁰H` is compact modulo punctures over an annulus
`Ann r₁ r₂ = {r₁ ≤ ‖z‖ ≤ r₂}` of ratio `> 1/λ` — so that finitely many powers of `σ` bring every
compact `K ⊂ ℂ*` into the annulus — then `S` is compact modulo punctures over every compact
`K ⊂ ℂ*`.  Punctured charts are transported by `shiftZ`, `ψ₁` and `κ` scaling by `λ^j`.

This is the first half of Rychlik Thm 8(2) (the second half, the cover of the annulus itself, is
`Work.EQ.compact_mod_punctures_of_tails`).  It is used by
`Submission.Work.EQ.exists_compact_regular_cycle`.

All declarations are prefixed `ac_` because the main one,
`ac_CompactModPunctures_of_annulus_cover`, replaces a declaration of the same statement that lived
in a now-withdrawn module; the prefix keeps any reconstruction from clashing with this one.
-/

namespace Work.EQ

open Complex Filter _root_.Topology

noncomputable section

open scoped Topology

/-- `eqLam a > 0` for `0 < a < 1`. -/
lemma ac_eqLam_pos {a : ℝ} (ha0 : 0 < a) (ha1 : a < 1) : 0 < eqLam a :=
  div_pos (by linarith) (by linarith)

/-- `((eqLam a : ℝ) : ℂ) ≠ 0`. -/
lemma ac_eqLamC_ne_zero {a : ℝ} (ha0 : 0 < a) (ha1 : a < 1) : ((eqLam a : ℝ) : ℂ) ≠ 0 :=
  Complex.ofReal_ne_zero.mpr (ne_of_gt (ac_eqLam_pos ha0 ha1))

/-- The norm of the real power `λ^j`: `‖(λ : ℂ)^j‖ = λ^j`. -/
lemma ac_norm_lamC_zpow {a : ℝ} (ha0 : 0 < a) (ha1 : a < 1) (j : ℤ) :
    ‖(eqLam a : ℂ) ^ j‖ = (eqLam a) ^ j := by
  rw [norm_zpow, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (ac_eqLam_pos ha0 ha1)]

/-- `‖ψ₁‖` after an integer shift of the chain scales by `λ^j`. -/
lemma ac_norm_psi1_shiftZ {a : ℝ} (ha0 : 0 < a) (ha1 : a < 1) (j : ℤ) (q : ChainData) :
    ‖(shiftZ a j q).2.1‖ = (eqLam a) ^ j * ‖q.2.1‖ := by
  rw [shiftZ_psi1, norm_mul, ac_norm_lamC_zpow ha0 ha1 j]

/-- `shiftZ a 0` is the identity. -/
@[simp] lemma ac_shiftZ_zero (a : ℝ) (p : ChainData) : shiftZ a 0 p = p := by
  have h : ∀ n : ℤ, (shiftZ a 0 p).1 n = p.1 n := by
    intro n; simp only [shiftZ_fst]; rw [add_zero]
  have h1 : (shiftZ a 0 p).2.1 = p.2.1 := by
    show ((eqLam a : ℝ) : ℂ) ^ (0 : ℤ) * p.2.1 = p.2.1
    rw [zpow_zero, one_mul]
  have h2 : (shiftZ a 0 p).2.2 = p.2.2 := by
    show p.2.2 / ((eqLam a : ℝ) : ℂ) ^ (0 : ℤ) = p.2.2
    rw [zpow_zero, div_one]
  exact Prod.ext (funext h) (Prod.ext h1 h2)

/-- The integer shifts are injective. -/
lemma ac_shiftZ_injective {a : ℝ} (ha0 : 0 < a) (ha1 : a < 1) (j : ℤ) :
    Function.Injective (shiftZ a j) := by
  intro p q hpq
  have h := congrArg (shiftZ a (-j)) hpq
  rw [(shiftZ_neg_apply ha0 ha1 j p).2, (shiftZ_neg_apply ha0 ha1 j q).2] at h
  exact h

/-- The forward `k`-fold shift maps a `σ`-invariant set into itself. -/
lemma ac_shiftZ_nat_mem {a : ℝ} (ha0 : 0 < a) (ha1 : a < 1) {S : Set ChainData}
    (hcyc : ∀ q : ChainData, q ∈ S ↔ hShift a q ∈ S) (k : ℕ) {q : ChainData} (hq : q ∈ S) :
    shiftZ a (k : ℤ) q ∈ S := by
  rw [← hShift_iterate_eq_shiftZ ha0 ha1 k q]
  induction k with
  | zero => simpa using hq
  | succ k ih => rw [Function.iterate_succ_apply']; exact (hcyc _).mp ih

/-- The inverse shift maps a `σ`-invariant set into itself. -/
lemma ac_shiftZ_neg_one_mem {a : ℝ} (ha0 : 0 < a) (ha1 : a < 1) {S : Set ChainData}
    (hcyc : ∀ q : ChainData, q ∈ S ↔ hShift a q ∈ S) {q : ChainData} (hq : q ∈ S) :
    shiftZ a (-1 : ℤ) q ∈ S := by
  refine (hcyc _).mpr ?_
  rw [hShift_eq_shiftZ, shiftZ_shiftZ ha0 ha1, show (1 : ℤ) + (-1) = 0 by ring]
  rw [ac_shiftZ_zero a q]
  exact hq

/-- An integer shift maps a `σ`-invariant set into itself. -/
lemma ac_shiftZ_mem_of_cyc {a : ℝ} (ha0 : 0 < a) (ha1 : a < 1) {S : Set ChainData}
    (hcyc : ∀ q : ChainData, q ∈ S ↔ hShift a q ∈ S) (j : ℤ) {q : ChainData} (hq : q ∈ S) :
    shiftZ a j q ∈ S := by
  by_cases hj : 0 ≤ j
  · rw [show j = ((j.toNat : ℕ) : ℤ) from (Int.toNat_of_nonneg hj).symm]
    exact ac_shiftZ_nat_mem ha0 ha1 hcyc j.toNat hq
  · have hk : j = -(((-j).toNat : ℕ) : ℤ) := by
      rw [Int.toNat_of_nonneg (by omega)]; ring
    rw [hk]
    have : ∀ (k : ℕ) {r : ChainData}, r ∈ S → shiftZ a (-(k : ℤ)) r ∈ S := by
      intro k
      induction k with
      | zero => intro r hr; simpa using hr
      | succ k ih =>
        intro r hr
        have h1 : shiftZ a (-(k : ℤ)) (shiftZ a (-1 : ℤ) r) ∈ S := ih (ac_shiftZ_neg_one_mem ha0 ha1 hcyc hr)
        rw [shiftZ_shiftZ ha0 ha1] at h1
        rwa [show -(k : ℤ) + (-1 : ℤ) = -(((k + 1 : ℕ)) : ℤ) by push_cast; ring] at h1
    exact this _ hq

/-- A positive lower bound for `‖·‖` on a compact set not containing `0`. -/
lemma ac_exists_norm_lower {K : Set ℂ} (hK : IsCompact K) (h0 : (0 : ℂ) ∉ K) :
    ∃ m : ℝ, 0 < m ∧ ∀ x ∈ K, m ≤ ‖x‖ := by
  rcases K.eq_empty_or_nonempty with h | hne
  · exact ⟨1, one_pos, by simp [h]⟩
  · obtain ⟨x₀, hx₀, hmin⟩ := hK.exists_isMinOn hne continuous_norm.continuousOn
    refine ⟨‖x₀‖, norm_pos_iff.mpr (fun hx => h0 (hx ▸ hx₀)), fun x hx => hmin hx⟩

/-- An upper bound for `‖·‖` on a compact set. -/
lemma ac_exists_norm_upper {K : Set ℂ} (hK : IsCompact K) :
    ∃ M : ℝ, ∀ x ∈ K, ‖x‖ ≤ M := by
  rcases K.eq_empty_or_nonempty with h | hne
  · exact ⟨0, by simp [h]⟩
  · obtain ⟨x₀, -, hmax⟩ := hK.exists_isMaxOn hne continuous_norm.continuousOn
    exact ⟨‖x₀‖, fun x hx => hmax hx⟩

/-- **Punctured charts are transported by the integer shifts.**  The chart
`ζ ↦ shiftZ a j (e ζ)` is a punctured chart centred at `λ^j u₀` with the same exponent `k`. -/
lemma ac_puncturedChart_shiftZ {a : ℝ} (ha0 : 0 < a) (ha1 : a < 1) {h : ℂ → ℂ}
    {e : ℂ → ChainData} {u₀ : ℂ} {k : ℕ} (he : IsPuncturedChart a h e u₀ k) (j : ℤ) :
    IsPuncturedChart a h (fun ζ => shiftZ a j (e ζ)) (((eqLam a : ℝ) : ℂ) ^ j * u₀) k := by
  obtain ⟨hk, hu₀, κ, hκ, hmem, hinj, hcont, hmer, hmer'⟩ := he
  have hlam : ((eqLam a : ℝ) : ℂ) ≠ 0 := ac_eqLamC_ne_zero ha0 ha1
  refine ⟨hk, mul_ne_zero (zpow_ne_zero _ hlam) hu₀,
    ((eqLam a : ℝ) : ℂ) ^ j * κ, mul_ne_zero (zpow_ne_zero _ hlam) hκ, ?_, ?_, ?_, ?_, ?_⟩
  · intro ζ hζ
    obtain ⟨hH0, hpsi⟩ := hmem ζ hζ
    refine ⟨mem_H0_shiftZ ha0 ha1 hH0 j, ?_⟩
    rw [shiftZ_psi1, hpsi]; ring
  · rintro ζ hζ ζ' hζ' heq
    exact hinj hζ hζ' (ac_shiftZ_injective ha0 ha1 j heq)
  · exact (continuous_shiftZ a j).continuousOn.comp hcont (fun ζ _ => Set.mem_univ _)
  · have heq : (fun ζ => (shiftZ a j (e ζ)).2.2)
        = fun ζ => (e ζ).2.2 * (((eqLam a : ℝ) : ℂ) ^ j)⁻¹ := by
      funext ζ; rw [shiftZ_psi2, div_eq_mul_inv]
    rw [heq]
    exact hmer.mul (analyticAt_const.meromorphicAt)
  · intro n
    have heq : (fun ζ => ((shiftZ a j (e ζ)).1 n).1) = fun ζ => ((e ζ).1 (n + j)).1 := by
      funext ζ; rw [shiftZ_fst]
    have heq2 : (fun ζ => ((shiftZ a j (e ζ)).1 n).2) = fun ζ => ((e ζ).1 (n + j)).2 := by
      funext ζ; rw [shiftZ_fst]
    rw [heq, heq2]
    exact ⟨(hmer' (n + j)).1, (hmer' (n + j)).2⟩

/-- **Transport of an annulus cover to the whole punctured plane.**

If `S` is invariant under the shift (`hcyc`) and `S ∩ {ψ₁ ∈ Ann r₁ r₂}` is covered by a compact
subset of `⁰H` together with finitely many punctured charts, and the annulus has ratio `> 1/λ`, then
`S` is compact modulo punctures over every compact `K ⊂ ℂ*`. -/
theorem ac_CompactModPunctures_of_annulus_cover {a : ℝ} (ha0 : 0 < a) (ha1 : a < 1)
    {h : ℂ → ℂ} {S : Set ChainData}
    (hcyc : ∀ q : ChainData, q ∈ S ↔ hShift a q ∈ S)
    {r₁ r₂ : ℝ} (hr₁ : 0 < r₁) (hr₂ : r₁ < r₂) (hratio : r₂ / r₁ > 1 / eqLam a)
    (hcover : ∃ (C : Set ChainData) (m : ℕ) (e : Fin m → ℂ → ChainData) (u₀ : Fin m → ℂ)
        (k : Fin m → ℕ),
      IsCompact C ∧ C ⊆ H0 a h ∧ (∀ i, IsPuncturedChart a h (e i) (u₀ i) (k i)) ∧
      S ∩ {q | q.2.1 ∈ Ann r₁ r₂} ⊆ C ∪ ⋃ i, (e i) '' (Metric.ball (0 : ℂ) (1 / 2) \ {0})) :
    CompactModPunctures a h S := by
  classical
  intro K hK h0
  obtain ⟨C, m, e, u₀, k, hCcpt, hCH0, hchart, hcov⟩ := hcover
  by_cases hKne : K.Nonempty
  · obtain ⟨x₀, hx₀⟩ := hKne
    obtain ⟨m₀, hm₀pos, hm₀⟩ := ac_exists_norm_lower hK h0
    obtain ⟨M₀, hM₀⟩ := ac_exists_norm_upper hK
    have hmM : m₀ ≤ M₀ := le_trans (hm₀ x₀ hx₀) (hM₀ x₀ hx₀)
    obtain ⟨J, hJ⟩ := exists_finset_zpow_annulus ha0 ha1 hr₁ hr₂ hratio hm₀pos hmM
    let Idx : Type := {x : ℤ // x ∈ J} × Fin m
    let M : ℕ := Fintype.card Idx
    let enc : Idx ≃ Fin M := Fintype.equivFin Idx
    refine ⟨⋃ j ∈ (J : Set ℤ), shiftZ a (-j) '' C, ?_, ?_, M,
      (fun i => fun ζ => shiftZ a (-((enc.symm i).1).val) (e (enc.symm i).2 ζ)),
      (fun i => (((eqLam a : ℝ) : ℂ) ^ (-((enc.symm i).1).val)) * u₀ (enc.symm i).2),
      (fun i => k (enc.symm i).2), ?_, ?_⟩
    · exact J.finite_toSet.isCompact_biUnion (fun j _ => hCcpt.image (continuous_shiftZ a (-j)))
    · intro q hq
      simp only [Set.mem_iUnion, Set.mem_image] at hq
      obtain ⟨j, _, y, hyC, hyq⟩ := hq
      rw [← hyq]
      exact mem_H0_shiftZ ha0 ha1 (hCH0 hyC) (-j)
    · intro i
      exact ac_puncturedChart_shiftZ ha0 ha1 (hchart (enc.symm i).2) (-((enc.symm i).1).val)
    · rintro q ⟨hqS, hqK⟩
      have hnorm_lo : m₀ ≤ ‖q.2.1‖ := hm₀ _ hqK
      have hnorm_hi : ‖q.2.1‖ ≤ M₀ := hM₀ _ hqK
      obtain ⟨j, hjJ, hjlo, hjhi⟩ := hJ ‖q.2.1‖ hnorm_lo hnorm_hi
      have hq'S : shiftZ a j q ∈ S := ac_shiftZ_mem_of_cyc ha0 ha1 hcyc j hqS
      have hpsi_norm : ‖(shiftZ a j q).2.1‖ = (eqLam a) ^ j * ‖q.2.1‖ :=
        ac_norm_psi1_shiftZ ha0 ha1 j q
      have hann : (shiftZ a j q).2.1 ∈ Ann r₁ r₂ := by
        refine ⟨?_, ?_⟩
        · rw [hpsi_norm]; exact hjlo
        · rw [hpsi_norm]; exact hjhi
      have hmem := hcov ⟨hq'S, hann⟩
      rcases hmem with hC | hU
      · left
        exact Set.mem_biUnion hjJ ⟨shiftZ a j q, hC, (shiftZ_neg_apply ha0 ha1 j q).2⟩
      · right
        simp only [Set.mem_iUnion, Set.mem_image] at hU ⊢
        obtain ⟨i, ζ, hζ, hζeq⟩ := hU
        refine ⟨enc (⟨j, hjJ⟩, i), ζ, hζ, ?_⟩
        have hsymm : enc.symm (enc (⟨j, hjJ⟩, i)) = (⟨j, hjJ⟩, i) := enc.symm_apply_apply _
        simp only [hsymm]
        show shiftZ a (-j) (e i ζ) = q
        rw [hζeq, (shiftZ_neg_apply ha0 ha1 j q).2]
  · rw [Set.not_nonempty_iff_eq_empty] at hKne
    subst hKne
    exact ⟨∅, isCompact_empty, Set.empty_subset _, 0, (fun i : Fin 0 => i.elim0),
      (fun i : Fin 0 => i.elim0), (fun i : Fin 0 => i.elim0), (fun i : Fin 0 => i.elim0),
      by simp⟩

end

end Work.EQ
