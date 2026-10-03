/-
# Matrix rings over von Neumann regular rings are von Neumann regular

If `U` is a von Neumann regular ring then so is `Matrix (Fin n) (Fin n) U` for every `n`.

The proof has two steps:

* `Module.End U (Fin n → U)` is von Neumann regular.  The range `M = p.range` of an
  endomorphism `p` is a finitely generated submodule of the free module `U^n`; the auxiliary
  lemma below shows it is the range of an idempotent endomorphism `e`.  Since `M` is a direct
  summand of the free module `U^n` it is projective, so the surjection `p : U^n → M` splits,
  and a splitting together with `e` produces a weak inverse of `p`.
* `Matrix (Fin n) (Fin n) U` acts on `U^n` by `Matrix.toLinearMapRight'`, which is a ring
  anti-isomorphism onto `Module.End U (Fin n → U)`; regularity transfers along it.
-/
import Mathlib
import Submission.Work.ORHughesFree.StarRegular
import Submission.Work.ORHughesFree.StarRegular.exists_idempotent_range_span_singleton

set_option autoImplicit false
set_option maxHeartbeats 1000000

namespace Work.ORHughesFree.StarRegular

open Work.ORHughesFree

/-- Over a von Neumann regular ring `S`, every finitely generated submodule of `S^n`
(presented as `Submodule.span S (Set.range v)`) is the range of an idempotent endomorphism
of `S^n`. -/
theorem exists_idempotent_range_span_aux {S : Type*} [Ring S] [VonNeumannRegularRing S]
    {n k : ℕ} (v : Fin k → (Fin n → S)) :
    ∃ e : Module.End S (Fin n → S), e * e = e ∧
      LinearMap.range e = Submodule.span S (Set.range v) := by
  revert n
  induction k with
  | zero =>
    intro n v
    refine ⟨0, by simp, ?_⟩
    have h : Set.range v = ∅ := by
      ext x; simp only [Set.mem_range, Set.mem_empty_iff_false, iff_false, not_exists]
      exact fun i => Fin.elim0 i
    rw [h, Submodule.span_empty, LinearMap.range_zero]
  | succ k ih =>
    intro n v
    obtain ⟨e', he', hrange'⟩ := ih (fun i : Fin k => v i.succ)
    obtain ⟨q, hq, hqrange⟩ := exists_idempotent_range_span_singleton (v 0 - e' (v 0))
    have hefix' : ∀ x : Fin n → S, e' (e' x) = e' x := by
      intro x; change (e' * e') x = e' x; rw [he']
    have he'w : e' (v 0 - e' (v 0)) = 0 := by rw [map_sub, hefix', sub_self]
    have he'qapply : ∀ x : Fin n → S, e' (q x) = 0 := by
      intro x
      have hx : q x ∈ Submodule.span S ({v 0 - e' (v 0)} : Set (Fin n → S)) := by
        rw [← hqrange]; exact LinearMap.mem_range_self q x
      rw [Submodule.mem_span_singleton] at hx
      obtain ⟨r, hr⟩ := hx
      rw [← hr, map_smul, he'w, smul_zero]
    have he'q : e' * q = 0 := by
      apply LinearMap.ext; intro x
      rw [Module.End.mul_eq_comp, LinearMap.comp_apply, he'qapply, LinearMap.zero_apply]
    have hone : (1 - e') * q = q := by rw [sub_mul, one_mul, he'q, sub_zero]
    have hqq : (q * (1 - e')) * (q * (1 - e')) = q * (1 - e') := by
      rw [show (q * (1 - e')) * (q * (1 - e')) = q * ((1 - e') * q) * (1 - e') by
        noncomm_ring, hone, hq]
    have he'q'' : e' * (q * (1 - e')) = 0 := by rw [← mul_assoc, he'q, zero_mul]
    have hq''e' : (q * (1 - e')) * e' = 0 := by
      rw [mul_assoc, sub_mul, one_mul, he', sub_self, mul_zero]
    have hp2 : (e' + q * (1 - e')) * (e' + q * (1 - e')) = e' + q * (1 - e') := by
      rw [show (e' + q * (1 - e')) * (e' + q * (1 - e')) =
          e' * e' + e' * (q * (1 - e')) + (q * (1 - e')) * e'
            + (q * (1 - e')) * (q * (1 - e')) by noncomm_ring,
        he', he'q'', hq''e', hqq]
      abel
    have hq''apply : ∀ x, (q * (1 - e')) x = q ((1 - e') x) := fun x => rfl
    have honeapply : ∀ x, (1 - e') x = x - e' x := by
      intro x; rw [LinearMap.sub_apply, Module.End.one_apply]
    have hrange_eq : LinearMap.range (e' + q * (1 - e')) =
        LinearMap.range e' ⊔ LinearMap.range (q * (1 - e')) := by
      apply le_antisymm
      · rintro y ⟨x, rfl⟩
        exact add_mem (Submodule.mem_sup_left (LinearMap.mem_range_self e' x))
          (Submodule.mem_sup_right (LinearMap.mem_range_self (q * (1 - e')) x))
      · rw [sup_le_iff]
        constructor
        · rintro y ⟨x, rfl⟩
          refine ⟨e' x, ?_⟩
          rw [LinearMap.add_apply, hefix']
          have : (q * (1 - e')) (e' x) = 0 := by
            rw [hq''apply, honeapply, hefix', sub_self, map_zero]
          rw [this, add_zero]
        · rintro y ⟨x, rfl⟩
          refine ⟨(q * (1 - e')) x, ?_⟩
          have h1 : e' (q ((1 - e') x)) = 0 := he'qapply _
          have h2 : q ((1 - e') (q ((1 - e') x))) = q ((1 - e') x) := by
            have h := congrArg (fun f : Module.End S (Fin n → S) => f x) hqq
            simp only [Module.End.mul_eq_comp, LinearMap.comp_apply] at h
            exact h
          rw [LinearMap.add_apply, hq''apply, hq''apply, h1, h2, zero_add]
    have hrange_q'' : LinearMap.range (q * (1 - e')) = LinearMap.range q := by
      apply le_antisymm
      · rintro y ⟨x, rfl⟩
        exact LinearMap.mem_range_self q ((1 - e') x)
      · rintro y ⟨x, rfl⟩
        have hy : (1 - e') (q x) = q x := by rw [honeapply, he'qapply x, sub_zero]
        refine ⟨q x, ?_⟩
        rw [hq''apply, hy]
        change (q * q) x = q x
        rw [hq]
    refine ⟨e' + q * (1 - e'), hp2, ?_⟩
    rw [hrange_eq, hrange_q'', hrange', hqrange]
    have hrange_v : Set.range v = insert (v 0) (Set.range (fun i : Fin k => v i.succ)) := by
      ext x
      simp only [Set.mem_range, Set.mem_insert_iff]
      constructor
      · rintro ⟨i, rfl⟩
        rcases Fin.eq_zero_or_eq_succ i with h | ⟨j, rfl⟩
        · exact Or.inl (congr_arg v h)
        · exact Or.inr ⟨j, rfl⟩
      · rintro (h | ⟨j, rfl⟩)
        · exact ⟨0, h.symm⟩
        · exact ⟨j.succ, rfl⟩
    rw [hrange_v, Submodule.span_insert]
    have h2 : e' (v 0) ∈ Submodule.span S (Set.range (fun i : Fin k => v i.succ)) := by
      rw [← hrange']; exact LinearMap.mem_range_self e' (v 0)
    have hw : v 0 - e' (v 0) ∈ Submodule.span S ({v 0 - e' (v 0)} : Set (Fin n → S)) :=
      Submodule.subset_span (Set.mem_singleton _)
    refine le_antisymm ?_ ?_
    · rw [sup_le_iff]
      refine ⟨le_sup_right, ?_⟩
      rw [Submodule.span_le]
      intro z hz
      rw [Set.mem_singleton_iff] at hz
      rw [hz]
      have h1 : v 0 ∈ Submodule.span S ({v 0} : Set (Fin n → S)) :=
        Submodule.subset_span (Set.mem_singleton _)
      exact sub_mem (Submodule.mem_sup_left h1) (Submodule.mem_sup_right h2)
    · rw [sup_le_iff]
      refine ⟨?_, le_sup_left⟩
      rw [Submodule.span_le]
      intro z hz
      rw [Set.mem_singleton_iff] at hz
      rw [hz]
      have hsum : e' (v 0) + (v 0 - e' (v 0)) ∈
          Submodule.span S (Set.range (fun i : Fin k => v i.succ)) ⊔
            Submodule.span S ({(v 0 - e' (v 0))} : Set (Fin n → S)) :=
        add_mem (Submodule.mem_sup_left h2) (Submodule.mem_sup_right hw)
      rwa [show e' (v 0) + (v 0 - e' (v 0)) = v 0 from by abel] at hsum

/-- If `S` is a von Neumann regular ring, then so is the ring of `S`-linear endomorphisms of
the free module `S^n`. -/
theorem vonNeumannRegularRing_moduleEnd {S : Type*} [Ring S] [VonNeumannRegularRing S] (n : ℕ) :
    VonNeumannRegularRing (Module.End S (Fin n → S)) := by
  constructor
  intro p
  obtain ⟨e, he, herange⟩ :=
    exists_idempotent_range_span_aux (fun i : Fin n => p (Pi.single i 1))
  have hspan : Submodule.span S (Set.range (Pi.basisFun S (Fin n))) = ⊤ :=
    (Pi.basisFun S (Fin n)).span_eq
  have hbasis : Set.range (Pi.basisFun S (Fin n)) =
      Set.range (fun i : Fin n => (Pi.single i 1 : Fin n → S)) := by
    congr 1 with i; rw [Pi.basisFun_apply]
  have hrange_p : LinearMap.range p =
      Submodule.span S (Set.range fun i : Fin n => p (Pi.single i 1)) := by
    calc LinearMap.range p = Submodule.map p ⊤ := (Submodule.map_top p).symm
      _ = Submodule.map p (Submodule.span S (Set.range (Pi.basisFun S (Fin n)))) := by
            rw [hspan]
      _ = Submodule.span S (p '' Set.range (Pi.basisFun S (Fin n))) := Submodule.map_span p _
      _ = _ := by rw [hbasis, ← Set.range_comp]; rfl
  have heq : LinearMap.range e = LinearMap.range p := by rw [herange, hrange_p]
  have hefix : ∀ y : Fin n → S, y ∈ LinearMap.range e → e y = y := by
    intro y hy
    obtain ⟨z, hz⟩ := hy
    rw [← hz]
    change (e ∘ₗ e) z = e z
    rw [← Module.End.mul_eq_comp, he]
  have hmem : ∀ x : Fin n → S, e x ∈ LinearMap.range p := by
    intro x; rw [← heq]; exact LinearMap.mem_range_self e x
  let s : (Fin n → S) →ₗ[S] LinearMap.range p := e.codRestrict _ hmem
  have hscomp : s.comp (Submodule.subtype (LinearMap.range p)) = LinearMap.id := by
    apply LinearMap.ext; intro m
    apply Subtype.ext
    change e (m : Fin n → S) = (m : Fin n → S)
    exact hefix _ (by rw [heq]; exact m.2)
  have hproj : Module.Projective S (LinearMap.range p) :=
    Module.Projective.of_split (Submodule.subtype _) s hscomp
  have hcod : ∀ x : Fin n → S, p x ∈ LinearMap.range p := fun x => LinearMap.mem_range_self p x
  have hsurj : (p.codRestrict (LinearMap.range p) hcod).range = ⊤ := by
    rw [LinearMap.range_eq_top]
    intro y
    obtain ⟨x, hx⟩ := y.2
    exact ⟨x, Subtype.ext hx⟩
  obtain ⟨q₁, hq₁⟩ :=
    (p.codRestrict (LinearMap.range p) hcod).exists_rightInverse_of_surjective hsurj
  refine ⟨q₁.comp s, ?_⟩
  rw [Module.End.mul_eq_comp, Module.End.mul_eq_comp]
  apply LinearMap.ext; intro x
  show p (q₁ (s (p x))) = p x
  have h1 : p (q₁ (s (p x))) = (s (p x) : Fin n → S) := by
    have h := LinearMap.congr_fun hq₁ (s (p x))
    simp only [LinearMap.comp_apply, LinearMap.id_apply] at h
    exact congrArg Subtype.val h
  rw [h1]
  change e (p x) = p x
  exact hefix _ (by rw [heq]; exact LinearMap.mem_range_self p x)

theorem vonNeumannRegularRing_matrix {U : Type*} [Ring U] [VonNeumannRegularRing U] (n : ℕ) :
    VonNeumannRegularRing (Matrix (Fin n) (Fin n) U) := by
  haveI : VonNeumannRegularRing (Module.End U (Fin n → U)) :=
    vonNeumannRegularRing_moduleEnd (S := U) n
  constructor
  intro A
  obtain ⟨φ, hφ⟩ := (inferInstance : VonNeumannRegularRing (Module.End U (Fin n → U)))
    |>.exists_mul_inverse (Matrix.toLinearMapRight' A)
  refine ⟨Matrix.toLinearMapRight'.symm φ, ?_⟩
  apply Matrix.toLinearMapRight'.injective
  have h1 : Matrix.toLinearMapRight' (Matrix.toLinearMapRight'.symm φ) = φ :=
    LinearEquiv.apply_symm_apply _ _
  rw [Matrix.toLinearMapRight'_mul, Matrix.toLinearMapRight'_mul, h1]
  simpa [Module.End.mul_eq_comp, LinearMap.comp_assoc] using hφ

end Work.ORHughesFree.StarRegular
