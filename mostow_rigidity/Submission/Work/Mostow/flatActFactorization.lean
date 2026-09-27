import Mathlib
import Submission.Work.Mostow.flatActBasic

/-!
# Factorisation of a flat (horospherical) displacement into bounded steps

Let `Γ ≤ PO n 1`, `ξ ∈ Sph n` a boundary point, and assume that the `Γ`-stabiliser of `ξ` acts
level-preservingly on the horospheres of `ξ` and that the flat displacements `flatAct ξ γ 0` of
stabiliser elements form an `R`-dense subset of the flat space `ξ^⊥`.  Then every `γ ∈ Γ` fixing
`ξ` is a product of at most `⌈‖flatAct ξ γ 0‖ / R⌉ + 2` elements of `Γ` fixing `ξ`, each of whose
flat displacements (from `0`) is bounded by `3 * R`.

The proof walks outwards along the segment from `0` to `flatAct ξ γ 0` in `ξ^⊥`, subdivided into
`⌈‖v‖/R⌉ + 1` pieces of length at most `R`, choosing for each intermediate point `x k` an element
`g k` of the stabiliser whose flat displacement is within `R` of `x k`.  The key identity is that
the flat displacement of `g k⁻¹ * g l` is the *difference* of the flat displacements of `g k` and
`g l`:

  `‖flatAct ξ (g⁻¹ * h) 0‖ = ‖flatAct ξ h 0 - flatAct ξ g 0‖`   (`flatAct_inv_mul_norm`),

so only the *increments* along the chain, and not the (large) intermediate displacements themselves,
appear in the list.  The resulting factorisation
`γ = g 0 * (g 0⁻¹ * g 1) * (g 1⁻¹ * g 2) * ⋯ * (g (m-1)⁻¹ * γ)`
has all factors of flat displacement `≤ 3 * R`.
-/

set_option linter.unusedVariables false

namespace Work.Mostow

open Submission.Mostow LeanEval.Geometry.MostowRigidity

variable {n : ℕ}

/-- The base point is on the level-one horosphere of every boundary point. -/
theorem flatAct_lev_zero (ξ : E n) : lev ξ (0 : E n) = 1 := by
  simp [lev, tpart]

/-- Level preservation passes to inverses. -/
theorem flatAct_lev_inv (hA : POBasic n) {ξ : E n} {g : PO n 1}
    (hg : ∀ u : E n, lev ξ (g • u) = lev ξ u) :
    ∀ u : E n, lev ξ (g⁻¹ • u) = lev ξ u := by
  intro u
  calc lev ξ (g⁻¹ • u) = lev ξ (g • (g⁻¹ • u)) := (hg (g⁻¹ • u)).symm
    _ = lev ξ u := by rw [← hA.mul_smul, mul_inv_cancel, hA.one_smul]

/-- For level-preserving elements `g, h` fixing `ξ`, the flat displacement of `g⁻¹ * h` is the
Euclidean distance in `ξ^⊥` between the flat displacements of `g` and `h`.

Indeed `flatAct ξ g⁻¹` is an isometry (of `ξ^⊥`) carrying `flatAct ξ g 0` to `0`, so it measures
exactly the difference of the two displacements. -/
theorem flatAct_inv_mul_norm {ξ : E n} (hξ : ξ ∈ Sph n) (hA : POBasic n) (hI : HypIsoData n)
    {g h : PO n 1} (hg : bd g ξ = ξ) (hh : bd h ξ = ξ)
    (hglev : ∀ u : E n, lev ξ (g • u) = lev ξ u)
    (hhlev : ∀ u : E n, lev ξ (h • u) = lev ξ u) :
    ‖flatAct ξ (g⁻¹ * h) (0 : E n)‖ = ‖flatAct ξ h (0 : E n) - flatAct ξ g (0 : E n)‖ := by
  have hgi : bd g⁻¹ ξ = ξ := bd_inv_of hξ hA hg
  have hgilev : ∀ u : E n, lev ξ (g⁻¹ • u) = lev ξ u := flatAct_lev_inv hA hglev
  have hz : inner ℝ (0 : E n) ξ = 0 := by simp
  have h0g : lev ξ (g • (0 : E n)) = 1 := by rw [hglev]; exact flatAct_lev_zero ξ
  have h0h : lev ξ (h • (0 : E n)) = 1 := by rw [hhlev]; exact flatAct_lev_zero ξ
  have h0gi : lev ξ (g⁻¹ • (0 : E n)) = 1 := by rw [hgilev]; exact flatAct_lev_zero ξ
  have hcomp : flatAct ξ g⁻¹ (flatAct ξ g (0 : E n)) = 0 := by
    have h := flatAct_comp hξ hA hI hgi hg h0gi h0g hz
    rw [inv_mul_cancel, flatAct_one hξ hA hz] at h
    exact h.symm
  calc ‖flatAct ξ (g⁻¹ * h) (0 : E n)‖
      = ‖flatAct ξ g⁻¹ (flatAct ξ h (0 : E n))‖ := by
        rw [flatAct_comp hξ hA hI hgi hh h0gi h0h hz]
    _ = ‖flatAct ξ g⁻¹ (flatAct ξ h (0 : E n)) - flatAct ξ g⁻¹ (flatAct ξ g (0 : E n))‖ := by
        rw [hcomp, sub_zero]
    _ = ‖flatAct ξ h (0 : E n) - flatAct ξ g (0 : E n)‖ :=
        flatAct_isometry hξ hA hI hgi h0gi (flatAct_mem hξ h (0 : E n))
          (flatAct_mem hξ g (0 : E n))

/-- Two consecutive points of the subdivision of the segment `[0, v]` into `⌈‖v‖/R⌉ + 1` equal
pieces are at distance at most `R`. -/
theorem flatAct_norm_step_le (v : E n) {R : ℝ} (hR : 0 < R) (k : ℕ) :
    ‖(((k : ℝ) + 1) / ((Nat.ceil (‖v‖ / R) + 1 : ℕ) : ℝ)) • v
      - ((k : ℝ) / ((Nat.ceil (‖v‖ / R) + 1 : ℕ) : ℝ)) • v‖ ≤ R := by
  set m : ℕ := Nat.ceil (‖v‖ / R) + 1 with hm
  have hmpos : (0 : ℝ) < (m : ℝ) := by
    have : 0 < m := by omega
    exact_mod_cast this
  have hstep : (((k : ℝ) + 1) / (m : ℝ)) • v - ((k : ℝ) / (m : ℝ)) • v
      = ((1 : ℝ) / (m : ℝ)) • v := by
    rw [← sub_smul]
    congr 1
    rw [div_sub_div_same, add_sub_cancel_left]
  have hkey : ‖v‖ ≤ R * (m : ℝ) := by
    have h1 : ‖v‖ / R ≤ (Nat.ceil (‖v‖ / R) : ℝ) := Nat.le_ceil _
    have h2 : (Nat.ceil (‖v‖ / R) : ℝ) ≤ (m : ℝ) := by
      rw [hm]; push_cast; linarith
    calc ‖v‖ = ‖v‖ / R * R := by rw [div_mul_cancel₀ _ (ne_of_gt hR)]
      _ ≤ (Nat.ceil (‖v‖ / R) : ℝ) * R := mul_le_mul_of_nonneg_right h1 (le_of_lt hR)
      _ ≤ (m : ℝ) * R := mul_le_mul_of_nonneg_right h2 (le_of_lt hR)
      _ = R * (m : ℝ) := by ring
  rw [hstep, norm_smul, Real.norm_eq_abs, abs_of_pos (div_pos one_pos hmpos), one_div,
    inv_mul_eq_div, div_le_iff₀ hmpos]
  exact hkey

/-- **Chain lemma.**  Let `x : ℕ → E n` be a sequence of points of `ξ^⊥` whose consecutive points
are at distance at most `R`, with `x 0 = 0`, and suppose the flat displacements of the stabiliser
of `ξ` in `Γ` are `R`-dense in `ξ^⊥`.  Then any `G ∈ Γ` fixing `ξ` with
`‖flatAct ξ G 0 - x k‖ ≤ R` is a product of at most `k + 1` elements of `Γ` fixing `ξ`, each of
flat displacement at most `3 * R`. -/
theorem flatActChain {n : ℕ} (hA : POBasic n) (hI : HypIsoData n)
    {Γ : Subgroup (PO n 1)} {ξ : E n} (hξ : ξ ∈ Sph n)
    (hlev : ∀ γ : Γ, bd ((γ : Γ) : PO n 1) ξ = ξ →
      ∀ u : E n, lev ξ (((γ : Γ) : PO n 1) • u) = lev ξ u)
    {R : ℝ} (hR : 0 < R)
    (hcov : ∀ x : E n, inner ℝ x ξ = 0 → ∃ γ : Γ,
      bd ((γ : Γ) : PO n 1) ξ = ξ ∧
      ‖flatAct ξ (((γ : Γ) : PO n 1)) (0 : E n) - x‖ ≤ R)
    (x : ℕ → E n) (hx0 : x 0 = 0) (hxm : ∀ k, inner ℝ (x k) ξ = 0)
    (hxstep : ∀ k, ‖x (k + 1) - x k‖ ≤ R) :
    ∀ (k : ℕ) (G : Γ), bd ((G : Γ) : PO n 1) ξ = ξ →
      ‖flatAct ξ (((G : Γ) : PO n 1)) (0 : E n) - x k‖ ≤ R →
      ∃ l : List Γ,
        l.length ≤ k + 1 ∧
        (∀ g ∈ l, bd ((g : Γ) : PO n 1) ξ = ξ ∧
          ‖flatAct ξ (((g : Γ) : PO n 1)) (0 : E n)‖ ≤ 3 * R) ∧
        l.prod = G := by
  intro k
  induction k with
  | zero =>
    intro G hG hGx
    have hnorm : ‖flatAct ξ (((G : Γ) : PO n 1)) (0 : E n)‖ ≤ 3 * R := by
      have h1 : ‖flatAct ξ (((G : Γ) : PO n 1)) (0 : E n)‖ ≤ R := by
        simpa [hx0] using hGx
      linarith
    refine ⟨[G], by simp, ?_, by simp⟩
    intro g hg
    rw [List.mem_singleton] at hg
    subst hg
    exact ⟨hG, hnorm⟩
  | succ k ih =>
    intro G hG hGx
    obtain ⟨Gk, hGk_bd, hGk_x⟩ := hcov (x k) (hxm k)
    obtain ⟨lk, hlen, hgood, hprod⟩ := ih Gk hGk_bd hGk_x
    have hcoe : (((Gk⁻¹ * G : Γ)) : PO n 1)
        = (((Gk : Γ)) : PO n 1)⁻¹ * (((G : Γ)) : PO n 1) := by
      rw [Subgroup.coe_mul, Subgroup.coe_inv]
    have hbd : bd (((Gk⁻¹ * G : Γ)) : PO n 1) ξ = ξ := by
      rw [hcoe]
      exact bd_mul_of hξ hA (bd_inv_of hξ hA hGk_bd) hG
    have hnorm : ‖flatAct ξ (((Gk⁻¹ * G : Γ)) : PO n 1) (0 : E n)‖ ≤ 3 * R := by
      have hkey : ‖flatAct ξ (((Gk⁻¹ * G : Γ)) : PO n 1) (0 : E n)‖
          = ‖flatAct ξ (((G : Γ)) : PO n 1) (0 : E n)
              - flatAct ξ (((Gk : Γ)) : PO n 1) (0 : E n)‖ :=
        flatAct_inv_mul_norm hξ hA hI hGk_bd hG (hlev Gk hGk_bd) (hlev G hG)
      rw [hkey]
      have hA1 : ‖flatAct ξ (((G : Γ)) : PO n 1) (0 : E n) - x (k + 1)‖ ≤ R := hGx
      have hA2 : ‖x (k + 1) - x k‖ ≤ R := hxstep k
      have hA3 : ‖x k - flatAct ξ (((Gk : Γ)) : PO n 1) (0 : E n)‖ ≤ R := by
        rw [norm_sub_rev]; exact hGk_x
      have htri : ‖flatAct ξ (((G : Γ)) : PO n 1) (0 : E n)
            - flatAct ξ (((Gk : Γ)) : PO n 1) (0 : E n)‖
          ≤ ‖flatAct ξ (((G : Γ)) : PO n 1) (0 : E n) - x (k + 1)‖
            + ‖x (k + 1) - x k‖
            + ‖x k - flatAct ξ (((Gk : Γ)) : PO n 1) (0 : E n)‖ := by
        rw [show flatAct ξ (((G : Γ)) : PO n 1) (0 : E n)
              - flatAct ξ (((Gk : Γ)) : PO n 1) (0 : E n)
              = (flatAct ξ (((G : Γ)) : PO n 1) (0 : E n) - x (k + 1))
                + (x (k + 1) - x k)
                + (x k - flatAct ξ (((Gk : Γ)) : PO n 1) (0 : E n)) from by abel]
        exact norm_add₃_le
      linarith
    refine ⟨lk ++ [Gk⁻¹ * G], ?_, ?_, ?_⟩
    · rw [List.length_append, List.length_singleton]
      exact Nat.add_le_add_right hlen 1
    · intro g hg
      rw [List.mem_append] at hg
      rcases hg with hg | hg
      · exact hgood g hg
      · rw [List.mem_singleton] at hg
        subst hg
        exact ⟨hbd, hnorm⟩
    · rw [List.prod_append, List.prod_singleton, hprod]
      exact mul_inv_cancel_left Gk G

theorem flatActFactorization {n : ℕ} (hA : Work.Mostow.POBasic n) (hI : Work.Mostow.HypIsoData n)
    {Γ : Subgroup (LeanEval.Geometry.MostowRigidity.PO n 1)} {ξ : Submission.Mostow.E n}
    (hξ : ξ ∈ Submission.Mostow.Sph n)
    (hlev : ∀ γ : Γ,
      Submission.Mostow.bd ((γ : Γ) : LeanEval.Geometry.MostowRigidity.PO n 1) ξ = ξ →
      ∀ u : Submission.Mostow.E n,
        Work.Mostow.lev ξ (((γ : Γ) : LeanEval.Geometry.MostowRigidity.PO n 1) • u)
          = Work.Mostow.lev ξ u)
    {R : ℝ} (hR : 0 < R)
    (hcov : ∀ x : Submission.Mostow.E n, inner ℝ x ξ = 0 → ∃ γ : Γ,
      Submission.Mostow.bd ((γ : Γ) : LeanEval.Geometry.MostowRigidity.PO n 1) ξ = ξ ∧
      ‖Work.Mostow.flatAct ξ (((γ : Γ) : LeanEval.Geometry.MostowRigidity.PO n 1))
        (0 : Submission.Mostow.E n) - x‖ ≤ R)
    (γ : Γ)
    (hγ : Submission.Mostow.bd ((γ : Γ) : LeanEval.Geometry.MostowRigidity.PO n 1) ξ = ξ) :
    ∃ l : List Γ,
      l.length ≤ Nat.ceil (‖Work.Mostow.flatAct ξ (((γ : Γ) : LeanEval.Geometry.MostowRigidity.PO n 1))
        (0 : Submission.Mostow.E n)‖ / R) + 2 ∧
      (∀ g ∈ l, Submission.Mostow.bd ((g : Γ) : LeanEval.Geometry.MostowRigidity.PO n 1) ξ = ξ ∧
        ‖Work.Mostow.flatAct ξ (((g : Γ) : LeanEval.Geometry.MostowRigidity.PO n 1))
          (0 : Submission.Mostow.E n)‖ ≤ 3 * R) ∧
      l.prod = γ := by
  classical
  set v : E n := flatAct ξ (((γ : Γ) : PO n 1)) (0 : E n) with hv
  let m : ℕ := Nat.ceil (‖v‖ / R) + 1
  have hm : m = Nat.ceil (‖v‖ / R) + 1 := rfl
  have hmpos : (0 : ℝ) < (m : ℝ) := by
    have : 0 < m := by omega
    exact_mod_cast this
  let x : ℕ → E n := fun k => ((k : ℝ) / (m : ℝ)) • v
  have hxdef : ∀ k, x k = ((k : ℝ) / (m : ℝ)) • v := fun k => rfl
  have hv0 : inner ℝ v ξ = 0 := flatAct_mem hξ _ _
  have hx0 : x 0 = 0 := by
    rw [hxdef 0]
    simp
  have hxm : ∀ k, inner ℝ (x k) ξ = 0 := by
    intro k
    rw [hxdef k, real_inner_smul_left, hv0, mul_zero]
  have hxstep : ∀ k, ‖x (k + 1) - x k‖ ≤ R := by
    intro k
    have hk : x (k + 1) - x k
        = (((k : ℝ) + 1) / (m : ℝ)) • v - ((k : ℝ) / (m : ℝ)) • v := by
      rw [hxdef (k + 1), hxdef k,
        show ((↑(k + 1) : ℝ)) = (k : ℝ) + 1 from by push_cast; ring]
    rw [hk]
    exact flatAct_norm_step_le v hR k
  have hxlast : ‖flatAct ξ (((γ : Γ) : PO n 1)) (0 : E n) - x m‖ ≤ R := by
    have hxmm : x m = v := by
      rw [hxdef m, div_self (ne_of_gt hmpos), one_smul]
    rw [hxmm, hv, sub_self, norm_zero]
    exact le_of_lt hR
  obtain ⟨l, hlen, hgood, hprod⟩ :=
    flatActChain hA hI hξ hlev hR hcov x hx0 hxm hxstep m γ hγ hxlast
  refine ⟨l, ?_, hgood, hprod⟩
  rw [hm] at hlen
  omega

end Work.Mostow
