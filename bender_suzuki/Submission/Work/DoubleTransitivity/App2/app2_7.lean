import Mathlib
import Submission.Work.DoubleTransitivity.Action
import Submission.Work.DoubleTransitivity.App2.app2_5

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

/-!
# Peterfalvi, Appendix II (7)

Setting: `X` is a finite group acting `2`-transitively on a set `E`.  For every pair of distinct
points `u ≠ v` there is a subgroup `Q ≤ X_u` which is normal in the point stabiliser `X_u`,
regular on `E \ {u}`, and such that every `h ∈ X_u` has a *unique* decomposition
`h = q * d` with `q ∈ Q` and `d ∈ X_u ⊓ X_v` (the source's "`D` has a normal complement `Q` in
`H`").  Under this hypothesis the centraliser of any `Y ≤ X_u ⊓ X_v` which fixes at least three
points acts `2`-transitively on its set of fixed points.

The mathematical proof is as follows.  Fix a pair `u ≠ v` and put `Q`, `D = X_u ⊓ X_v` as in the
hypothesis, with `Y ≤ D`.

* The uniqueness of the decomposition forces `Q ⊓ D = 1`: if `q ∈ Q ⊓ D`, then `q = q * 1` and
  `q = 1 * q` are two decompositions of the same element, so the `Q`-component is both `q` and
  `1`.
* Consequently `Q` acts *freely* at `v`: if `q ∈ Q` and `q • v = v`, then
  `q ∈ Q ⊓ X_u ⊓ X_v = 1`.  (Transitivity of `Q` on `E \ {u}` extends this to any point `≠ u`.)
* Let `c ∈ E_Y`, `c ≠ u`, and `q ∈ Q` with `q • v = c` (regularity of `Q`).  For `y ∈ Y ≤ X_u`
  normality gives `y q y⁻¹ ∈ Q`, and `(y q y⁻¹) • v = y • c = c`, so freeness gives
  `y q y⁻¹ = q`.  Hence `q ∈ Q ⊓ C_X(Y)`.
* Uniqueness of such a `q` is again freeness, and `Q ⊓ C_X(Y)` fixes `u`.  So for every
  `u ∈ E_Y` the point stabiliser of `C_X(Y)` at `u` admits a subgroup (`Q ⊓ C_X(Y)`, for any
  `v ∈ E_Y \ {u}`) which is sharply transitive on `E_Y \ {u}`; in particular `C_X(Y)` has
  transitive point stabilisers on `E_Y`.
* A group with transitive point stabilisers on a set with at least three points is
  `2`-transitive, which is the final assembly below (the third point is what `3 ≤ |E_Y|` is for).
-/

set_option linter.style.haveILetI false
set_option linter.unusedVariables false

namespace Work.DoubleTransitivity.App2

open Work.DoubleTransitivity

/-! ## Elementary auxiliary lemmas -/

/-- The centraliser of `Y` preserves the set of points fixed by `Y`. -/
theorem smul_mem_fixedBySub_of_mem_centralizer {X E : Type} [Group X] [MulAction X E]
    {Y : Subgroup X} {g : X} (hg : g ∈ Subgroup.centralizer (Y : Set X)) {s : E}
    (hs : s ∈ fixedBySub Y) : g • s ∈ fixedBySub Y := by
  intro m hm
  have hcomm : m * g = g * m := Subgroup.mem_centralizer_iff.mp hg m hm
  calc m • (g • s) = (m * g) • s := (mul_smul m g s).symm
    _ = (g * m) • s := by rw [hcomm]
    _ = g • (m • s) := mul_smul g m s
    _ = g • s := by rw [mem_fixedBySub.mp hs m hm]

/-- A subgroup all of whose elements fix `u` is contained in the stabiliser of `u`. -/
theorem le_stabilizer_of_mem_fixedBySub {X E : Type} [Group X] [MulAction X E]
    {Y : Subgroup X} {u : E} (hu : u ∈ fixedBySub Y) :
    Y ≤ MulAction.stabilizer X u :=
  fun m hm => MulAction.mem_stabilizer_iff.mpr ((mem_fixedBySub.mp hu) m hm)

/-- Pigeonhole: a set with at least three elements contains an element different from two given
distinct elements. -/
theorem app2_7_third_point {E : Type} {S : Set E} {c d : E}
    (hc : c ∈ S) (hd : d ∈ S) (hcd : c ≠ d) (hbig : 3 ≤ S.ncard) :
    ∃ e ∈ S, e ≠ c ∧ e ≠ d := by
  by_contra h
  have hsub : S ⊆ ({c, d} : Set E) := by
    intro x hx
    by_contra hxc
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff, not_or] at hxc
    exact h ⟨x, hx, hxc.1, hxc.2⟩
  have hle : S.ncard ≤ ({c, d} : Set E).ncard := Set.ncard_le_ncard hsub
  rw [Set.ncard_pair hcd] at hle
  omega

/-! ## The core configuration -/

/-- **Peterfalvi, Appendix II (7), core configuration.**  Let `u ≠ v`, let `Q ≤ X_u` be normal
in the point stabiliser `X_u`, regular on `E \ {u}`, and such that every `h ∈ X_u` has a unique
decomposition `h = q * d` with `q ∈ Q`, `d ∈ X_u ⊓ X_v`.  Let `Y ≤ X_u ⊓ X_v`.  Then `Q ⊓ C_X(Y)`
fixes `u`, and for every `c ∈ E_Y` with `c ≠ u` there is a *unique* `q ∈ Q ⊓ C_X(Y)` with
`q • v = c`; i.e. `Q ⊓ C_X(Y)` is sharply transitive on the fixed points of `Y` other than `u`. -/
theorem app2_7_core {X E : Type} [Group X] [MulAction X E]
    {u v : E} (huv : u ≠ v) {Q Y : Subgroup X}
    (hQu : Q ≤ MulAction.stabilizer X u)
    (hQn : MulAction.stabilizer X u ≤ Subgroup.normalizer (Q : Set X))
    (hQreg : IsRegularOnSub Q ({u}ᶜ : Set E))
    (hdec : ∀ h ∈ MulAction.stabilizer X u, ∃! q : Q,
      ∃ d ∈ MulAction.stabilizer X u ⊓ MulAction.stabilizer X v, (q : X) * d = h)
    (hY : Y ≤ MulAction.stabilizer X u ⊓ MulAction.stabilizer X v) :
    (Q ⊓ Subgroup.centralizer (Y : Set X) ≤ MulAction.stabilizer X u) ∧
    v ∈ (fixedBySub Y : Set E) ∧
    (∀ c ∈ (fixedBySub Y : Set E), c ≠ u →
      ∃! q : (Q ⊓ Subgroup.centralizer (Y : Set X) : Subgroup X), (q : X) • v = c) := by
  -- uniqueness of the decomposition forces `Q ⊓ (X_u ⊓ X_v) = 1`
  have hQD : Q ⊓ (MulAction.stabilizer X u ⊓ MulAction.stabilizer X v) = ⊥ := by
    rw [eq_bot_iff]
    intro q hq
    obtain ⟨q₀, -, huniq⟩ := hdec q hq.2.1
    have h1 : (⟨q, hq.1⟩ : Q) = q₀ := huniq ⟨q, hq.1⟩ ⟨1, by simp, by simp⟩
    have h2 : (1 : Q) = q₀ := huniq 1 ⟨q, hq.2, by simp⟩
    have heq : (⟨q, hq.1⟩ : Q) = 1 := h1.trans h2.symm
    have hq1 : q = 1 := congrArg Subtype.val heq
    simpa using hq1
  -- `Q` acts freely at `v`
  have hfree_v : ∀ q ∈ Q, q • v = v → q = 1 := by
    intro q hq hqv
    have hmem : q ∈ Q ⊓ (MulAction.stabilizer X u ⊓ MulAction.stabilizer X v) :=
      ⟨hq, hQu hq, MulAction.mem_stabilizer_iff.mpr hqv⟩
    rw [hQD] at hmem
    simpa using hmem
  refine ⟨fun q hq => hQu hq.1, ?_, ?_⟩
  · intro m hm
    exact MulAction.mem_stabilizer_iff.mp (hY hm).2
  · intro c hc hcu
    -- existence: `Q` is transitive on `E \ {u}`
    obtain ⟨q, hqQ, hqv⟩ :=
      hQreg.1 v (by simpa using Ne.symm huv) c (by simpa using hcu)
    have hqC : q ∈ Subgroup.centralizer (Y : Set X) := by
      rw [Subgroup.mem_centralizer_iff]
      intro y hy
      have hyD : y ∈ MulAction.stabilizer X u ⊓ MulAction.stabilizer X v := hY hy
      have hyN : y ∈ Subgroup.normalizer (Q : Set X) := hQn hyD.1
      have hyq : y * q * y⁻¹ ∈ Q := (Subgroup.mem_normalizer_iff.mp hyN q).mp hqQ
      have hyv : y⁻¹ • v = v :=
        MulAction.mem_stabilizer_iff.mp ((MulAction.stabilizer X v).inv_mem hyD.2)
      have hyc : y • c = c := (mem_fixedBySub.mp hc) y hy
      have hstep : (y * q * y⁻¹) • v = c := by
        rw [mul_smul, mul_smul, hyv, hqv, hyc]
      have hvv : (q⁻¹ * (y * q * y⁻¹)) • v = v := by
        rw [mul_smul, hstep, ← hqv, inv_smul_smul]
      have hmemQ : q⁻¹ * (y * q * y⁻¹) ∈ Q := Q.mul_mem (Q.inv_mem hqQ) hyq
      have hone : q⁻¹ * (y * q * y⁻¹) = 1 := hfree_v _ hmemQ hvv
      have hyq_eq : y * q * y⁻¹ = q := by
        have h : q * (q⁻¹ * (y * q * y⁻¹)) = q := by rw [hone, mul_one]
        rwa [← mul_assoc, mul_inv_cancel, one_mul] at h
      calc y * q = (y * q * y⁻¹) * y := by group
        _ = q * y := by rw [hyq_eq]
    refine ⟨⟨q, hqQ, hqC⟩, by simpa using hqv, ?_⟩
    -- uniqueness, again by freeness at `v`
    intro y hy
    apply Subtype.ext
    have hmem : q⁻¹ * (y : X) ∈ Q := Q.mul_mem (Q.inv_mem hqQ) y.2.1
    have hvv : (q⁻¹ * (y : X)) • v = v := by
      rw [mul_smul, hy, ← hqv, inv_smul_smul]
    have hone : q⁻¹ * (y : X) = 1 := hfree_v _ hmem hvv
    have hyq : (y : X) = q := by
      have h : q * (q⁻¹ * (y : X)) = q := by rw [hone, mul_one]
      rwa [← mul_assoc, mul_inv_cancel, one_mul] at h
    simpa using hyq

/-! ## Appendix II (7) -/

theorem app2_7 {X E : Type} [Group X] [MulAction X E] [Finite X]
    (h2 : MulAction.IsMultiplyPretransitive X E 2)
    (hreg : ∀ a b : E, a ≠ b → ∃ Q : Subgroup X, Q ≤ MulAction.stabilizer X a ∧
      MulAction.stabilizer X a ≤ Subgroup.normalizer (Q : Set X) ∧
      IsRegularOnSub Q ({a}ᶜ : Set E) ∧
      (∀ h ∈ MulAction.stabilizer X a, ∃! q : Q,
        ∃ d ∈ MulAction.stabilizer X a ⊓ MulAction.stabilizer X b, (q : X) * d = h))
    {Y : Subgroup X} {a b : E} (hab : a ≠ b)
    (hY : Y ≤ MulAction.stabilizer X a ⊓ MulAction.stabilizer X b)
    (hbig : 3 ≤ (fixedBySub Y : Set E).ncard) :
    IsTwoTransitiveOnSub (Subgroup.centralizer (Y : Set X)) (fixedBySub Y : Set E) := by
  -- the point stabiliser of `C_X(Y)` at `u` is transitive on `E_Y \ {u}`
  have hpt : ∀ u ∈ (fixedBySub Y : Set E), ∀ v ∈ (fixedBySub Y : Set E), v ≠ u →
      ∀ c ∈ (fixedBySub Y : Set E), c ≠ u →
      ∃ g ∈ Subgroup.centralizer (Y : Set X), g • u = u ∧ g • v = c := by
    intro u hu v hv hvu c hc hcu
    obtain ⟨Q, hQu, hQn, hQreg, hdec⟩ := hreg u v (Ne.symm hvu)
    have hYuv : Y ≤ MulAction.stabilizer X u ⊓ MulAction.stabilizer X v :=
      le_inf (le_stabilizer_of_mem_fixedBySub hu) (le_stabilizer_of_mem_fixedBySub hv)
    obtain ⟨hQC, -, huniq⟩ := app2_7_core (Ne.symm hvu) hQu hQn hQreg hdec hYuv
    obtain ⟨q, hqv, -⟩ := huniq c hc hcu
    exact ⟨(q : X), q.2.2, MulAction.mem_stabilizer_iff.mp (hQu q.2.1), hqv⟩
  -- transitivity of `C_X(Y)` on `E_Y`
  have htrans : ∀ c ∈ (fixedBySub Y : Set E), ∀ d ∈ (fixedBySub Y : Set E),
      ∃ g ∈ Subgroup.centralizer (Y : Set X), g • c = d := by
    intro c hc d hd
    by_cases hcd : c = d
    · exact ⟨1, Subgroup.one_mem _, by rw [one_smul, hcd]⟩
    · obtain ⟨e, he, hec, hed⟩ := app2_7_third_point hc hd hcd hbig
      obtain ⟨g, hg, _, hgcd⟩ := hpt e he c hc (Ne.symm hec) d hd (Ne.symm hed)
      exact ⟨g, hg, hgcd⟩
  -- transitivity of the point stabilisers gives `2`-transitivity
  intro c hc d hd hcd c' hc' d' hd' hcd'
  obtain ⟨g, hg, hgc⟩ := htrans c hc c' hc'
  have hgd : g • d ∈ (fixedBySub Y : Set E) :=
    smul_mem_fixedBySub_of_mem_centralizer hg hd
  have hgdc' : g • d ≠ c' := by
    intro h
    rw [← hgc] at h
    exact hcd (MulAction.injective g h).symm
  obtain ⟨h', hh', hh'c', hh'd'⟩ := hpt c' hc' (g • d) hgd hgdc' d' hd' (Ne.symm hcd')
  refine ⟨h' * g, (Subgroup.centralizer (Y : Set X)).mul_mem hh' hg, ?_, ?_⟩
  · show (h' * g) • c = c'
    rw [mul_smul, hgc, hh'c']
  · show (h' * g) • d = d'
    rw [mul_smul, hh'd']

end Work.DoubleTransitivity.App2
