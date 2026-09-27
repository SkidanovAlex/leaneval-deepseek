import Mathlib
import Submission.Mostow.GapADefs
import Submission.Work.Mostow.poAction

/-! Guidance from the project lead (the requester):

# Low-dimensional copies (lead's request). The strata / Kazhdan-Margulis / geodesic-stratum chapters need the toolkit in
# every dimension k >= 1 (strata of dimension 1, 2, ... inside H^n). Your statement is the SAME Prop as an already-PROVED
# area lemma, only with a weaker dimension hypothesis:
#   poAction_ge1      <- Work.Mostow.poAction (proved for 3 <= n; its proof only uses 2 <= n via poCenter).
#                        n = 1 needs its own centre argument: A central in O(1,1) commutes with diag(-1,1) and diag(1,-1)
#                        => A diagonal => A = diag(a,b), a,b in {+1,-1}; commuting with a boost forces a = b => A = +-1.
#   hypIsometry_ge1   <- Work.Mostow.hypIsometry (proved for 3 <= n). For n = 1: E 1 = R is H^1, isometries of R are
#                        x -> +-x + c, all realised by PO(1,1) (boosts = translations, diag(-1,1) = reflection).
#   classify_ge2      <- your geomFinite colleagues have `classifyProp n hn hA hI` (search Submission/Work/Mostow for
#                        classifyProp); restate/reprove for 2 <= n.
#   multThick_ge2     <- Work.Mostow.geomFiniteMultThick (PROVED in the geomFinite tree); restate for 2 <= n.
# COPY the existing proofs (import their modules; do not re-derive), check every use of the dimension hypothesis, and
# patch only the places that genuinely used 3 <= n. Never use `λ` as a variable name.
-/

namespace Work.Mostow

open Submission.Mostow LeanEval.Geometry.MostowRigidity MeasureTheory Matrix
open scoped Matrix

noncomputable section

variable {n : ℕ}

/-! ### The centre of `O(n,1)` for `n ≥ 1`

`Work.Mostow.poCenter` states the classification `center (O1 n) = {±1}` under the hypothesis
`2 ≤ n`, but its proof is completely dimension-free: it only tests a central element against the
diagonal sign matrices `diagSignElem b` (forcing diagonality) and against the hyperbolic boosts
`boostElem i` (forcing all diagonal entries to be equal), and then uses the defining relation of
`O(n,1)`.  We copy that proof with the hypothesis weakened to `1 ≤ n`; the same argument works
verbatim because a hyperbolic boost in the `(e_i, e_time)`-plane exists as soon as there is a
spatial coordinate `i : Fin n`. -/

/-- The centre of `O(n,1)` is `{±1}`, for every `n ≥ 1`. -/
theorem poCenter_ge1 (n : ℕ) (hn : 1 ≤ n) :
    ∀ A : O1 n, A ∈ Subgroup.center (O1 n) ↔ A = 1 ∨ A = -1 := by
  intro A
  constructor
  · intro hA
    rw [Subgroup.mem_center_iff] at hA
    -- (1) `A` commutes with the diagonal sign matrix with a `-1` at `b`, so all entries of
    -- `mat A` off the diagonal vanish.
    have hoff : ∀ a b : Fin n ⊕ Fin 1, a ≠ b → mat A a b = 0 := by
      intro a b hab
      have hentry : (mat (diagSignElem b) * mat A) a b = (mat A * mat (diagSignElem b)) a b := by
        have := congrArg (fun X : O1 n => mat X a b) (hA (diagSignElem b))
        simpa [mat_mul] using this
      simp only [mat_diagSignElem, diagSign, Matrix.diagonal_mul, Matrix.mul_diagonal] at hentry
      rw [if_neg hab] at hentry
      simp at hentry
      linarith
    -- (2) hence `mat A` is diagonal.
    have hdiag : mat A = Matrix.diagonal (fun c => mat A c c) := by
      ext a b
      by_cases hab : a = b
      · subst hab
        simp
      · rw [Matrix.diagonal_apply, if_neg hab]
        exact hoff a b hab
    -- (3) commuting with a boostMat_poCenterDefs equates the `i`-th spatial diagonal entry with the time entry.
    have hentry_eq : ∀ i : Fin n, mat A (Sum.inl i) (Sum.inl i) = mat A (Sum.inr 0) (Sum.inr 0) := by
      intro i
      have hb : (mat (boostElem i) * mat A) (Sum.inl i) (Sum.inr 0) =
                (mat A * mat (boostElem i)) (Sum.inl i) (Sum.inr 0) := by
        have := congrArg (fun X : O1 n => mat X (Sum.inl i) (Sum.inr 0)) (hA (boostElem i))
        simpa [mat_mul] using this
      rw [mat_boostElem i, hdiag, Matrix.diagonal_mul, Matrix.mul_diagonal] at hb
      simp only [boost_apply_spatial_time] at hb
      rw [mul_comm (mat A (Sum.inl i) (Sum.inl i)) ((3 : ℝ) / 4)] at hb
      exact (mul_left_cancel₀ (by norm_num : (3 : ℝ) / 4 ≠ 0) hb).symm
    -- (4) all diagonal entries of `mat A` are equal.
    have hconst : ∀ c : Fin n ⊕ Fin 1, mat A c c = mat A (Sum.inr 0) (Sum.inr 0) := by
      intro c
      rcases c with i | j
      · exact hentry_eq i
      · obtain rfl : j = 0 := Subsingleton.elim j 0
        rfl
    have hmat_const : mat A = Matrix.diagonal
        (fun _ : Fin n ⊕ Fin 1 => mat A (Sum.inr 0) (Sum.inr 0)) := by
      rw [hdiag, Matrix.diagonal_eq_diagonal_iff]
      exact hconst
    set e := mat A (Sum.inr 0) (Sum.inr 0) with he
    -- (5) the defining relation `(mat A)ᵀ J (mat A) = J` forces `e ^ 2 = 1`.
    have hesq : e ^ 2 = 1 := by
      have hcol := O1_form_col A
      rw [hmat_const, Matrix.diagonal_transpose, pmOneMat_eq_diagonal_poCenterDefs, mul_assoc,
        Matrix.diagonal_mul_diagonal, Matrix.diagonal_mul_diagonal,
        Matrix.diagonal_eq_diagonal_iff] at hcol
      have h0 := hcol (Sum.inr 0)
      simp only [jSign_inr] at h0
      nlinarith
    rw [← Matrix.smul_one_eq_diagonal] at hmat_const
    rcases sq_eq_one_iff.mp hesq with h | h
    · left
      apply mat_injective
      rw [hmat_const, h, one_smul, mat_one]
    · right
      apply mat_injective
      rw [hmat_const, h, neg_smul, one_smul, mat_neg, mat_one]
  · intro h
    rw [Subgroup.mem_center_iff]
    intro g
    rcases h with rfl | rfl
    · simp
    · apply mat_injective
      simp [mat_neg]

/-! ### Area T1 for `n ≥ 1`

The assembly below is the proof of `Work.Mostow.poAction`, whose only use of `3 ≤ n` was
`2 ≤ n`, used in turn only to invoke `poCenter`.  Every other ingredient
(`poSheet`, `poBdAlg`, `poBdReg`, `poActCont`, `poContDescent`) is stated for every `n : ℕ`,
so replacing `poCenter n hn2` by `poCenter_ge1 n hn` gives the statement for all `n ≥ 1`. -/

theorem poAction_ge1 (n : ℕ) (hn : 1 ≤ n) : POActionProp n := by
  obtain ⟨hsheet, htsignmul, hactOmul, hactOone, hactOneg⟩ := poSheet n
  obtain ⟨hbdmem, hbdneg, hbdmul, hbdone⟩ := poBdAlg n
  obtain ⟨hbdcont, hbdmeas⟩ := poBdReg n
  obtain ⟨hactcont, _htsigncont⟩ := poActCont n
  have hcen : ∀ A : O1 n, A ∈ Subgroup.center (O1 n) ↔ A = 1 ∨ A = -1 := poCenter_ge1 n hn
  -- central elements do not change `actO` or `bdO`
  have hactOcen : ∀ (B c : O1 n), c ∈ Subgroup.center (O1 n) → actO (B * c) = actO B := by
    intro B c hc
    funext u
    rcases (hcen c).1 hc with rfl | rfl
    · rw [mul_one]
    · rw [O1_mul_neg_one]; exact hactOneg B u
  have hbdOcen : ∀ (B c : O1 n), c ∈ Subgroup.center (O1 n) → bdO (B * c) = bdO B := by
    intro B c hc
    funext ξ
    rcases (hcen c).1 hc with rfl | rfl
    · rw [mul_one]
    · rw [O1_mul_neg_one]; exact hbdneg B ξ
  have hcen_of_mk : ∀ A : O1 n,
      (rep (A : PO n 1))⁻¹ * A ∈ Subgroup.center (O1 n) := by
    intro A
    exact QuotientGroup.eq.1 (QuotientGroup.out_eq' (A : PO n 1))
  have hactO_of_mk : ∀ A : O1 n, actO (rep (A : PO n 1)) = actO A := by
    intro A
    have hc := hcen_of_mk A
    have hA : A = rep (A : PO n 1) * ((rep (A : PO n 1))⁻¹ * A) := by
      rw [← mul_assoc, mul_inv_cancel, one_mul]
    have h2 : actO A = actO (rep (A : PO n 1)) := by
      conv_lhs => rw [hA]
      exact hactOcen _ _ hc
    exact h2.symm
  have hbdO_of_mk : ∀ A : O1 n, bdO (rep (A : PO n 1)) = bdO A := by
    intro A
    have hc := hcen_of_mk A
    have hA : A = rep (A : PO n 1) * ((rep (A : PO n 1))⁻¹ * A) := by
      rw [← mul_assoc, mul_inv_cancel, one_mul]
    have h2 : bdO A = bdO (rep (A : PO n 1)) := by
      conv_lhs => rw [hA]
      exact hbdOcen _ _ hc
    exact h2.symm
  -- clause 2
  have hsmul : ∀ (A : O1 n) (u : E n), (A : PO n 1) • u = actO A u := by
    intro A u
    show actO (rep (A : PO n 1)) u = actO A u
    rw [hactO_of_mk]
  -- clause 3
  have hbd_eq : ∀ (A : O1 n) (ξ : E n), ξ ∈ Sph n → bd (A : PO n 1) ξ = bdO A ξ := by
    intro A ξ _
    show bdO (rep (A : PO n 1)) ξ = bdO A ξ
    rw [hbdO_of_mk]
  -- clause 4
  have hone : ∀ u : E n, (1 : PO n 1) • u = u := by
    intro u
    rw [show (1 : PO n 1) = ((1 : O1 n) : PO n 1) from
          (QuotientGroup.mk_one (Subgroup.center (O1 n))).symm, hsmul, hactOone]
  -- clause 5
  have hmul : ∀ (g h : PO n 1) (u : E n), (g * h) • u = g • (h • u) := by
    intro g h u
    obtain ⟨A, rfl⟩ := QuotientGroup.mk_surjective g
    obtain ⟨B, rfl⟩ := QuotientGroup.mk_surjective h
    rw [← QuotientGroup.mk_mul, hsmul, hactOmul, ← hsmul, ← hsmul]
  -- clause 6
  have hfaith : ∀ g : PO n 1, (∀ u : E n, g • u = u) → g = 1 := by
    intro g hg
    have hfix : ∀ u : E n, actO (rep g) u = u := by
      intro u
      have hrep : ((rep g : O1 n) : PO n 1) = g := QuotientGroup.out_eq' g
      rw [← hsmul (rep g) u, hrep, hg u]
    have hlin : ∀ u : E n, mat (rep g) *ᵥ hlift u = tsign (rep g) • hlift u := by
      intro u
      have h1 : hlift u = tsign (rep g) • (mat (rep g) *ᵥ hlift u) := by
        conv_lhs => rw [← hfix u]
        exact hsheet (rep g) u
      have h2 := congrArg (fun v => tsign (rep g) • v) h1
      rw [smul_smul, tsign_sq, one_smul] at h2
      exact h2.symm
    have hmat : mat (rep g) = tsign (rep g) • 1 := mat_eq_smul_one_of _ _ hlin
    have hmat' := hmat
    have hA : rep g = 1 ∨ rep g = -1 := by
      rcases tsign_eq_one_or (rep g) with ht | ht
      · left
        rw [ht, one_smul] at hmat'
        exact mat_inj (by rw [hmat', mat_one])
      · right
        rw [ht] at hmat'
        simp only [neg_smul, one_smul] at hmat'
        exact mat_inj (by rw [hmat', mat_neg, mat_one])
    have hc : rep g ∈ Subgroup.center (O1 n) := (hcen (rep g)).2 hA
    rw [← QuotientGroup.out_eq' g]
    exact (QuotientGroup.eq_one_iff (rep g)).2 hc
  refine ⟨hcen, hsmul, hbd_eq, hone, hmul, hfaith,
    poContDescent n hactcont hsmul, ?_, ?_, ?_, ?_, ?_⟩
  · intro g ξ hξ; exact hbdmem (rep g) ξ hξ
  · intro ξ hξ
    have hrep1 : rep (1 : PO n 1) ∈ Subgroup.center (O1 n) :=
      (QuotientGroup.eq_one_iff (rep (1 : PO n 1))).1 (QuotientGroup.out_eq' 1)
    show bdO (rep (1 : PO n 1)) ξ = ξ
    have h1 : bdO (rep (1 : PO n 1)) = bdO 1 := by
      have hh := hbdOcen (1 : O1 n) (rep (1 : PO n 1)) hrep1
      rwa [one_mul] at hh
    rw [h1, hbdone]
  · intro g h ξ hξ
    obtain ⟨A, rfl⟩ := QuotientGroup.mk_surjective g
    obtain ⟨B, rfl⟩ := QuotientGroup.mk_surjective h
    rw [← QuotientGroup.mk_mul (Subgroup.center (O1 n)) A B]
    show bdO (rep ((A * B : O1 n) : PO n 1)) ξ = bdO (rep (A : PO n 1)) (bdO (rep (B : PO n 1)) ξ)
    rw [hbdO_of_mk, hbdO_of_mk, hbdO_of_mk]
    exact hbdmul A B ξ hξ
  · intro g; exact hbdcont (rep g)
  · intro g; exact hbdmeas (rep g)

end

end Work.Mostow
