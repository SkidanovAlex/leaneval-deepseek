import Mathlib
import Submission.Work.ORHughesFree.StarRegular
import Submission.Work.ORHughesFree.StarRegular.exists_idempotent_range_span_singleton

namespace Work.ORHughesFree.DivisionRank

/-- **Adding a cyclic submodule to a direct summand.**  If `P` is an idempotent endomorphism of
`Uⁿ` whose range is `M`, then `M ⊔ U∙w` is again the range of an idempotent endomorphism.

Indeed the mirror image of `M` is `range (id - P)`, and `w = P w + (id - P) w`.  The cyclic case
applied to `(id - P) w` gives an idempotent `r` with range `U∙((id - P) w)`; correcting it to
`r' = r ∘ (id - P)` makes it kill `M` and be killed by `P`, and `P + r'` is the required
idempotent. -/
theorem exists_projection_sup_singleton {U : Type*} [Ring U] [VonNeumannRegularRing U]
    (n : ℕ) (M : Submodule U (Fin n → U)) (w : Fin n → U)
    (P : (Fin n → U) →ₗ[U] (Fin n → U)) (hP : P.comp P = P) (hPr : P.range = M) :
    ∃ Q : (Fin n → U) →ₗ[U] (Fin n → U),
      Q.comp Q = Q ∧ Q.range = M ⊔ Submodule.span U ({w} : Set (Fin n → U)) := by
  classical
  let q : (Fin n → U) →ₗ[U] (Fin n → U) := LinearMap.id - P
  have hq : q.comp q = q := by
    show (LinearMap.id - P).comp (LinearMap.id - P) = LinearMap.id - P
    rw [LinearMap.comp_sub, LinearMap.comp_id, LinearMap.sub_comp, LinearMap.id_comp, hP,
      sub_self, sub_zero]
  have hPq : P.comp q = 0 := by
    show P.comp (LinearMap.id - P) = 0
    rw [LinearMap.comp_sub, LinearMap.comp_id, hP, sub_self]
  have hqP : q.comp P = 0 := by
    show (LinearMap.id - P).comp P = 0
    rw [LinearMap.sub_comp, LinearMap.id_comp, hP, sub_self]
  have hqrange : q.range = LinearMap.ker P := by
    ext y
    constructor
    · rintro ⟨x, rfl⟩
      show P (q x) = 0
      rw [← LinearMap.comp_apply, hPq, LinearMap.zero_apply]
    · intro hy
      have hy' : P y = 0 := LinearMap.mem_ker.mp hy
      refine ⟨y, ?_⟩
      show q y = y
      rw [show q = LinearMap.id - P from rfl, LinearMap.sub_apply, LinearMap.id_apply, hy',
        sub_zero]
  obtain ⟨r, hr, hrr⟩ := StarRegular.exists_idempotent_range_span_singleton (q w)
  have hr_comp : r.comp r = r := hr
  have hspan_le : Submodule.span U ({q w} : Set (Fin n → U)) ≤ q.range := by
    rw [Submodule.span_le, Set.singleton_subset_iff]
    exact LinearMap.mem_range_self q w
  have hPrr : P.comp r = 0 := by
    apply LinearMap.ext
    intro x
    show P (r x) = 0
    have hx : r x ∈ q.range := by
      have h1 : r x ∈ r.range := LinearMap.mem_range_self r x
      rw [hrr] at h1
      exact hspan_le h1
    rw [hqrange] at hx
    exact LinearMap.mem_ker.mp hx
  have hqr : q.comp r = r := by
    have hPqid : P + q = LinearMap.id := by
      show P + (LinearMap.id - P) = LinearMap.id
      abel
    have hsum : P.comp r + q.comp r = r := by
      rw [← LinearMap.add_comp, hPqid, LinearMap.id_comp]
    rw [hPrr, zero_add] at hsum
    exact hsum
  let r' : (Fin n → U) →ₗ[U] (Fin n → U) := r.comp q
  have hr'idem : r'.comp r' = r' := by
    show (r.comp q).comp (r.comp q) = r.comp q
    rw [LinearMap.comp_assoc, ← LinearMap.comp_assoc q r q, hqr, ← LinearMap.comp_assoc q r r,
      hr_comp]
  have hPr' : P.comp r' = 0 := by
    show P.comp (r.comp q) = 0
    rw [← LinearMap.comp_assoc, hPrr, LinearMap.zero_comp]
  have hr'P : r'.comp P = 0 := by
    show (r.comp q).comp P = 0
    rw [LinearMap.comp_assoc, hqP, LinearMap.comp_zero]
  have hQidem : (P + r').comp (P + r') = P + r' := by
    rw [LinearMap.add_comp, LinearMap.comp_add, LinearMap.comp_add, hP, hPr', hr'P, hr'idem]
    abel
  have hQrange : (P + r').range = P.range ⊔ r'.range := by
    apply le_antisymm
    · rintro y ⟨x, rfl⟩
      rw [LinearMap.add_apply]
      exact Submodule.add_mem_sup (LinearMap.mem_range_self P x) (LinearMap.mem_range_self r' x)
    · rw [sup_le_iff]
      constructor
      · rintro y ⟨x, rfl⟩
        refine ⟨P x, ?_⟩
        rw [LinearMap.add_apply]
        have h1 : P (P x) = P x := by rw [← LinearMap.comp_apply, hP]
        have h2 : r' (P x) = 0 := by
          rw [← LinearMap.comp_apply, hr'P, LinearMap.zero_apply]
        rw [h1, h2, add_zero]
      · rintro y ⟨x, rfl⟩
        refine ⟨r' x, ?_⟩
        rw [LinearMap.add_apply]
        have h1 : P (r' x) = 0 := by
          rw [← LinearMap.comp_apply, hPr', LinearMap.zero_apply]
        have h2 : r' (r' x) = r' x := by rw [← LinearMap.comp_apply, hr'idem]
        rw [h1, h2, zero_add]
  have hrr' : r'.range = Submodule.span U ({q w} : Set (Fin n → U)) := by
    apply le_antisymm
    · rintro y ⟨x, rfl⟩
      show r (q x) ∈ Submodule.span U ({q w} : Set (Fin n → U))
      rw [← hrr]
      exact LinearMap.mem_range_self r (q x)
    · rw [Submodule.span_le, Set.singleton_subset_iff]
      refine LinearMap.mem_range.mpr ⟨q w, ?_⟩
      show r (q (q w)) = q w
      rw [show q (q w) = q w from by rw [← LinearMap.comp_apply, hq]]
      have hmem : q w ∈ r.range := by
        rw [hrr]; exact Submodule.subset_span (Set.mem_singleton _)
      obtain ⟨z, hz⟩ := LinearMap.mem_range.mp hmem
      rw [← hz, ← LinearMap.comp_apply, hr_comp]
  refine ⟨P + r', hQidem, ?_⟩
  rw [hQrange, hrr', hPr]
  apply le_antisymm
  · rw [sup_le_iff]
    refine ⟨le_sup_left, ?_⟩
    rw [Submodule.span_le, Set.singleton_subset_iff]
    have hw : w ∈ M ⊔ Submodule.span U ({w} : Set (Fin n → U)) :=
      Submodule.mem_sup_right (Submodule.subset_span (Set.mem_singleton w))
    have hPw : P w ∈ M ⊔ Submodule.span U ({w} : Set (Fin n → U)) :=
      Submodule.mem_sup_left (by rw [← hPr]; exact LinearMap.mem_range_self P w)
    have hqww : q w = w - P w := by
      rw [show q = LinearMap.id - P from rfl, LinearMap.sub_apply, LinearMap.id_apply]
    rw [hqww]
    exact Submodule.sub_mem _ hw hPw
  · rw [sup_le_iff]
    refine ⟨le_sup_left, ?_⟩
    rw [Submodule.span_le, Set.singleton_subset_iff]
    have hqw : q w ∈ M ⊔ Submodule.span U ({q w} : Set (Fin n → U)) :=
      Submodule.mem_sup_right (Submodule.subset_span (Set.mem_singleton (q w)))
    have hPw : P w ∈ M ⊔ Submodule.span U ({q w} : Set (Fin n → U)) :=
      Submodule.mem_sup_left (by rw [← hPr]; exact LinearMap.mem_range_self P w)
    have hw : w = P w + q w := by
      rw [show q = LinearMap.id - P from rfl, LinearMap.sub_apply, LinearMap.id_apply]; abel
    have hmem : P w + q w ∈ M ⊔ Submodule.span U ({q w} : Set (Fin n → U)) :=
      Submodule.add_mem _ hPw hqw
    rwa [← hw] at hmem

/-- Every finitely generated submodule of `Uⁿ` generated by a finite set is the range of an
idempotent endomorphism. -/
theorem exists_projection_span_finset {U : Type*} [Ring U] [VonNeumannRegularRing U]
    (n : ℕ) (s : Finset (Fin n → U)) :
    ∃ P : (Fin n → U) →ₗ[U] (Fin n → U),
      P.comp P = P ∧ P.range = Submodule.span U (↑s : Set (Fin n → U)) := by
  classical
  induction s using Finset.induction_on with
  | empty =>
      refine ⟨0, by simp, ?_⟩
      rw [Finset.coe_empty, Submodule.span_empty, LinearMap.range_zero]
  | insert v s hv ih =>
      obtain ⟨P, hP, hPr⟩ := ih
      obtain ⟨Q, hQ, hQr⟩ :=
        exists_projection_sup_singleton n (Submodule.span U (↑s : Set (Fin n → U))) v P hP hPr
      refine ⟨Q, hQ, ?_⟩
      rw [hQr, Finset.coe_insert, Submodule.span_insert]
      exact sup_comm _ _

theorem regular_fgSubmodule_projection {U : Type*} [Ring U] [VonNeumannRegularRing U]
    (n : ℕ) (M : Submodule U (Fin n → U)) (hM : M.FG) :
    ∃ P : (Fin n → U) →ₗ[U] (Fin n → U), P.comp P = P ∧ P.range = M := by
  obtain ⟨s, hs⟩ := hM
  obtain ⟨P, hP, hPr⟩ := exists_projection_span_finset n s
  exact ⟨P, hP, by rw [hPr, hs]⟩

end Work.ORHughesFree.DivisionRank
