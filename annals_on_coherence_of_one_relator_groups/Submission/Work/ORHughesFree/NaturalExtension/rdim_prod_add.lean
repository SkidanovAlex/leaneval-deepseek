import Mathlib
import Submission.Work.ORHughesFree.SylvesterRank
import Submission.Work.ORHughesFree.StarRegular
import Submission.Work.ORHughesFree.StarRegular.vonNeumannRegularRing_matrix
import Submission.Work.ORHughesFree.NaturalExtension.DualityAPI
import Submission.Work.ORHughesFree.NaturalExtension.rdim_add_of_isCompl
import Submission.Work.ORHughesFree.NaturalExtension.rdim_map_of_leftInverse
import Submission.Work.ORHughesFree.NaturalExtension.rdim_eq_sSup_span

set_option autoImplicit false
set_option maxHeartbeats 1000000

universe u

namespace Work.ORHughesFree.NaturalExtension

open Matrix Work.ORHughesFree

section ProdHelpers

variable {R : Type u} [Ring R]
variable {n m : ℕ}

theorem prod_eq_sup_prod_bot (P : Submodule R (Fin n → R)) (Q : Submodule R (Fin m → R)) :
    Submodule.prod P Q = Submodule.prod P ⊥ ⊔ Submodule.prod ⊥ Q := by
  refine le_antisymm ?_ ?_
  · intro x hx
    rw [Submodule.mem_prod] at hx
    refine Submodule.mem_sup.mpr ⟨(x.1, 0), ?_, (0, x.2), ?_, ?_⟩
    · exact Submodule.mem_prod.mpr ⟨hx.1, Submodule.zero_mem _⟩
    · exact Submodule.mem_prod.mpr ⟨Submodule.zero_mem _, hx.2⟩
    · ext <;> simp
  · refine sup_le ?_ ?_
    · exact Submodule.prod_mono le_rfl bot_le
    · exact Submodule.prod_mono bot_le le_rfl

theorem isCompl_prod {P P' : Submodule R (Fin n → R)} {Q Q' : Submodule R (Fin m → R)}
    (hP : IsCompl P P') (hQ : IsCompl Q Q') :
    IsCompl (Submodule.prod P Q) (Submodule.prod P' Q') := by
  refine isCompl_iff.mpr ⟨disjoint_iff.mpr ?_, codisjoint_iff.mpr ?_⟩
  · rw [eq_bot_iff]
    intro x hx
    rw [Submodule.mem_inf, Submodule.mem_prod, Submodule.mem_prod] at hx
    have h1 : x.1 = 0 := by
      have : x.1 ∈ P ⊓ P' := Submodule.mem_inf.mpr ⟨hx.1.1, hx.2.1⟩
      simpa [hP.inf_eq_bot] using this
    have h2 : x.2 = 0 := by
      have : x.2 ∈ Q ⊓ Q' := Submodule.mem_inf.mpr ⟨hx.1.2, hx.2.2⟩
      simpa [hQ.inf_eq_bot] using this
    rw [Submodule.mem_bot R]
    exact Prod.ext h1 h2
  · rw [eq_top_iff]
    intro x _
    rw [Submodule.mem_sup]
    have h1 : x.1 ∈ P ⊔ P' := by rw [hP.sup_eq_top]; exact Submodule.mem_top
    have h2 : x.2 ∈ Q ⊔ Q' := by rw [hQ.sup_eq_top]; exact Submodule.mem_top
    obtain ⟨a, ha, a', ha', haa⟩ := Submodule.mem_sup.mp h1
    obtain ⟨b, hb, b', hb', hbb⟩ := Submodule.mem_sup.mp h2
    exact ⟨(a, b), Submodule.mem_prod.mpr ⟨ha, hb⟩, (a', b'),
      Submodule.mem_prod.mpr ⟨ha', hb'⟩, by ext <;> simp [haa, hbb]⟩

theorem prod_bot_eq_map_inl (P : Submodule R (Fin n → R)) :
    Submodule.prod P (⊥ : Submodule R (Fin m → R))
      = Submodule.map (LinearMap.inl R (Fin n → R) (Fin m → R)) P := by
  ext x
  constructor
  · intro hx
    rw [Submodule.mem_prod] at hx
    have hx2 : x.2 = 0 := (Submodule.mem_bot R).mp hx.2
    refine ⟨x.1, hx.1, ?_⟩
    rw [LinearMap.inl_apply]
    exact Prod.ext rfl (by rw [hx2])
  · intro hx
    rw [Submodule.mem_map] at hx
    obtain ⟨y, hy, rfl⟩ := hx
    rw [LinearMap.inl_apply, Submodule.mem_prod]
    exact ⟨hy, Submodule.zero_mem _⟩

theorem bot_prod_eq_map_inr (Q : Submodule R (Fin m → R)) :
    Submodule.prod (⊥ : Submodule R (Fin n → R)) Q
      = Submodule.map (LinearMap.inr R (Fin n → R) (Fin m → R)) Q := by
  ext x
  constructor
  · intro hx
    rw [Submodule.mem_prod] at hx
    have hx1 : x.1 = 0 := (Submodule.mem_bot R).mp hx.1
    refine ⟨x.2, hx.2, ?_⟩
    rw [LinearMap.inr_apply]
    exact Prod.ext (by rw [hx1]) rfl
  · intro hx
    rw [Submodule.mem_map] at hx
    obtain ⟨y, hy, rfl⟩ := hx
    rw [LinearMap.inr_apply, Submodule.mem_prod]
    exact ⟨Submodule.zero_mem _, hy⟩

end ProdHelpers

theorem rdim_prod_add_finSpan {R : Type u} [Ring R] [VonNeumannRegularRing R]
    (rk : SylvesterRank R) {n m ka kb : ℕ}
    (e : ((Fin n → R) × (Fin m → R)) ≃ₗ[R] (Fin (n + m) → R))
    (a : Fin ka → (Fin n → R)) (b : Fin kb → (Fin m → R)) :
    rdim rk (Submodule.map (e : ((Fin n → R) × (Fin m → R)) →ₗ[R] (Fin (n + m) → R))
      (Submodule.prod (Submodule.span R (Set.range a)) (Submodule.span R (Set.range b))))
      = rdim rk (Submodule.span R (Set.range a)) + rdim rk (Submodule.span R (Set.range b)) := by
  classical
  set P : Submodule R (Fin n → R) := Submodule.span R (Set.range a) with hP
  set Q : Submodule R (Fin m → R) := Submodule.span R (Set.range b) with hQ
  obtain ⟨p, hp, hpr⟩ := Work.ORHughesFree.StarRegular.exists_idempotent_range_span_aux a
  obtain ⟨q, hq, hqr⟩ := Work.ORHughesFree.StarRegular.exists_idempotent_range_span_aux b
  have hPrange : P = LinearMap.range p := by rw [hP]; exact hpr.symm
  have hQrange : Q = LinearMap.range q := by rw [hQ]; exact hqr.symm
  have hpcompl : IsCompl P (LinearMap.ker p) := by
    rw [hPrange]; exact LinearMap.IsIdempotentElem.isCompl hp
  have hqcompl : IsCompl Q (LinearMap.ker q) := by
    rw [hQrange]; exact LinearMap.IsIdempotentElem.isCompl hq
  have hsumP : rdim rk P + rdim rk (LinearMap.ker p) = (n : ℝ) :=
    rdim_add_of_isCompl rk hpcompl.sup_eq_top hpcompl.inf_eq_bot
  have hsumQ : rdim rk Q + rdim rk (LinearMap.ker q) = (m : ℝ) :=
    rdim_add_of_isCompl rk hqcompl.sup_eq_top hqcompl.inf_eq_bot
  have hcompl : IsCompl (Submodule.prod P Q)
      (Submodule.prod (LinearMap.ker p) (LinearMap.ker q)) := isCompl_prod hpcompl hqcompl
  have hsup_map : Submodule.map (e : ((Fin n → R) × (Fin m → R)) →ₗ[R] (Fin (n + m) → R))
        (Submodule.prod P Q)
      ⊔ Submodule.map (e : ((Fin n → R) × (Fin m → R)) →ₗ[R] (Fin (n + m) → R))
        (Submodule.prod (LinearMap.ker p) (LinearMap.ker q)) = ⊤ := by
    rw [← Submodule.map_sup, hcompl.sup_eq_top, Submodule.map_top,
      LinearMap.range_eq_top.mpr e.surjective]
  have hinf_map : Submodule.map (e : ((Fin n → R) × (Fin m → R)) →ₗ[R] (Fin (n + m) → R))
        (Submodule.prod P Q)
      ⊓ Submodule.map (e : ((Fin n → R) × (Fin m → R)) →ₗ[R] (Fin (n + m) → R))
        (Submodule.prod (LinearMap.ker p) (LinearMap.ker q)) = ⊥ := by
    rw [← Submodule.map_inf (e : ((Fin n → R) × (Fin m → R)) →ₗ[R] (Fin (n + m) → R))
      e.injective, hcompl.inf_eq_bot, Submodule.map_bot]
  have huv : rdim rk (Submodule.map (e : ((Fin n → R) × (Fin m → R)) →ₗ[R] (Fin (n + m) → R))
        (Submodule.prod P Q))
      + rdim rk (Submodule.map (e : ((Fin n → R) × (Fin m → R)) →ₗ[R] (Fin (n + m) → R))
        (Submodule.prod (LinearMap.ker p) (LinearMap.ker q))) = ((n + m : ℕ) : ℝ) :=
    rdim_add_of_isCompl rk hsup_map hinf_map
  have hmap1 : Submodule.map (e : ((Fin n → R) × (Fin m → R)) →ₗ[R] (Fin (n + m) → R))
        (Submodule.prod P Q)
      = Submodule.map (e : ((Fin n → R) × (Fin m → R)) →ₗ[R] (Fin (n + m) → R))
          (Submodule.prod P ⊥)
        ⊔ Submodule.map (e : ((Fin n → R) × (Fin m → R)) →ₗ[R] (Fin (n + m) → R))
          (Submodule.prod ⊥ Q) := by
    rw [prod_eq_sup_prod_bot P Q, Submodule.map_sup]
  have hmap1' : Submodule.map (e : ((Fin n → R) × (Fin m → R)) →ₗ[R] (Fin (n + m) → R))
        (Submodule.prod (LinearMap.ker p) (LinearMap.ker q))
      = Submodule.map (e : ((Fin n → R) × (Fin m → R)) →ₗ[R] (Fin (n + m) → R))
          (Submodule.prod (LinearMap.ker p) ⊥)
        ⊔ Submodule.map (e : ((Fin n → R) × (Fin m → R)) →ₗ[R] (Fin (n + m) → R))
          (Submodule.prod ⊥ (LinearMap.ker q)) := by
    rw [prod_eq_sup_prod_bot (LinearMap.ker p) (LinearMap.ker q), Submodule.map_sup]
  have hpsi1 : (((LinearMap.fst R (Fin n → R) (Fin m → R)) ∘ₗ
        (e.symm : (Fin (n + m) → R) →ₗ[R] ((Fin n → R) × (Fin m → R))))
      ∘ₗ ((e : ((Fin n → R) × (Fin m → R)) →ₗ[R] (Fin (n + m) → R))
        ∘ₗ LinearMap.inl R (Fin n → R) (Fin m → R))) = LinearMap.id := by
    apply LinearMap.ext; intro x
    simp [LinearMap.comp_apply, LinearMap.fst_apply, LinearMap.inl_apply]
  have hpsi2 : (((LinearMap.snd R (Fin n → R) (Fin m → R)) ∘ₗ
        (e.symm : (Fin (n + m) → R) →ₗ[R] ((Fin n → R) × (Fin m → R))))
      ∘ₗ ((e : ((Fin n → R) × (Fin m → R)) →ₗ[R] (Fin (n + m) → R))
        ∘ₗ LinearMap.inr R (Fin n → R) (Fin m → R))) = LinearMap.id := by
    apply LinearMap.ext; intro x
    simp [LinearMap.comp_apply, LinearMap.snd_apply, LinearMap.inr_apply]
  have hrdimA : rdim rk (Submodule.map (e : ((Fin n → R) × (Fin m → R)) →ₗ[R] (Fin (n + m) → R))
        (Submodule.prod P ⊥)) = rdim rk P := by
    have h : Submodule.map (e : ((Fin n → R) × (Fin m → R)) →ₗ[R] (Fin (n + m) → R))
          (Submodule.prod P ⊥)
        = Submodule.map ((e : ((Fin n → R) × (Fin m → R)) →ₗ[R] (Fin (n + m) → R))
          ∘ₗ LinearMap.inl R (Fin n → R) (Fin m → R)) P := by
      rw [prod_bot_eq_map_inl, Submodule.map_comp]
    rw [h]
    exact @rdim_map_of_leftInverse R _ rk n (n + m)
      ((e : ((Fin n → R) × (Fin m → R)) →ₗ[R] (Fin (n + m) → R))
        ∘ₗ LinearMap.inl R (Fin n → R) (Fin m → R))
      (((LinearMap.fst R (Fin n → R) (Fin m → R)) ∘ₗ
        (e.symm : (Fin (n + m) → R) →ₗ[R] ((Fin n → R) × (Fin m → R))))) hpsi1 P
  have hrdimB : rdim rk (Submodule.map (e : ((Fin n → R) × (Fin m → R)) →ₗ[R] (Fin (n + m) → R))
        (Submodule.prod ⊥ Q)) = rdim rk Q := by
    have h : Submodule.map (e : ((Fin n → R) × (Fin m → R)) →ₗ[R] (Fin (n + m) → R))
          (Submodule.prod ⊥ Q)
        = Submodule.map ((e : ((Fin n → R) × (Fin m → R)) →ₗ[R] (Fin (n + m) → R))
          ∘ₗ LinearMap.inr R (Fin n → R) (Fin m → R)) Q := by
      rw [bot_prod_eq_map_inr, Submodule.map_comp]
    rw [h]
    exact @rdim_map_of_leftInverse R _ rk m (n + m)
      ((e : ((Fin n → R) × (Fin m → R)) →ₗ[R] (Fin (n + m) → R))
        ∘ₗ LinearMap.inr R (Fin n → R) (Fin m → R))
      (((LinearMap.snd R (Fin n → R) (Fin m → R)) ∘ₗ
        (e.symm : (Fin (n + m) → R) →ₗ[R] ((Fin n → R) × (Fin m → R))))) hpsi2 Q
  have hrdimA' : rdim rk (Submodule.map (e : ((Fin n → R) × (Fin m → R)) →ₗ[R] (Fin (n + m) → R))
        (Submodule.prod (LinearMap.ker p) ⊥)) = rdim rk (LinearMap.ker p) := by
    have h : Submodule.map (e : ((Fin n → R) × (Fin m → R)) →ₗ[R] (Fin (n + m) → R))
          (Submodule.prod (LinearMap.ker p) ⊥)
        = Submodule.map ((e : ((Fin n → R) × (Fin m → R)) →ₗ[R] (Fin (n + m) → R))
          ∘ₗ LinearMap.inl R (Fin n → R) (Fin m → R)) (LinearMap.ker p) := by
      rw [prod_bot_eq_map_inl, Submodule.map_comp]
    rw [h]
    exact @rdim_map_of_leftInverse R _ rk n (n + m)
      ((e : ((Fin n → R) × (Fin m → R)) →ₗ[R] (Fin (n + m) → R))
        ∘ₗ LinearMap.inl R (Fin n → R) (Fin m → R))
      (((LinearMap.fst R (Fin n → R) (Fin m → R)) ∘ₗ
        (e.symm : (Fin (n + m) → R) →ₗ[R] ((Fin n → R) × (Fin m → R))))) hpsi1 (LinearMap.ker p)
  have hrdimB' : rdim rk (Submodule.map (e : ((Fin n → R) × (Fin m → R)) →ₗ[R] (Fin (n + m) → R))
        (Submodule.prod ⊥ (LinearMap.ker q))) = rdim rk (LinearMap.ker q) := by
    have h : Submodule.map (e : ((Fin n → R) × (Fin m → R)) →ₗ[R] (Fin (n + m) → R))
          (Submodule.prod ⊥ (LinearMap.ker q))
        = Submodule.map ((e : ((Fin n → R) × (Fin m → R)) →ₗ[R] (Fin (n + m) → R))
          ∘ₗ LinearMap.inr R (Fin n → R) (Fin m → R)) (LinearMap.ker q) := by
      rw [bot_prod_eq_map_inr, Submodule.map_comp]
    rw [h]
    exact @rdim_map_of_leftInverse R _ rk m (n + m)
      ((e : ((Fin n → R) × (Fin m → R)) →ₗ[R] (Fin (n + m) → R))
        ∘ₗ LinearMap.inr R (Fin n → R) (Fin m → R))
      (((LinearMap.snd R (Fin n → R) (Fin m → R)) ∘ₗ
        (e.symm : (Fin (n + m) → R) →ₗ[R] ((Fin n → R) × (Fin m → R))))) hpsi2 (LinearMap.ker q)
  have hu : rdim rk (Submodule.map (e : ((Fin n → R) × (Fin m → R)) →ₗ[R] (Fin (n + m) → R))
        (Submodule.prod P Q)) ≤ rdim rk P + rdim rk Q := by
    rw [hmap1]
    calc rdim rk (Submodule.map (e : ((Fin n → R) × (Fin m → R)) →ₗ[R] (Fin (n + m) → R))
            (Submodule.prod P ⊥)
          ⊔ Submodule.map (e : ((Fin n → R) × (Fin m → R)) →ₗ[R] (Fin (n + m) → R))
            (Submodule.prod ⊥ Q))
        ≤ rdim rk (Submodule.map (e : ((Fin n → R) × (Fin m → R)) →ₗ[R] (Fin (n + m) → R))
            (Submodule.prod P ⊥))
          + rdim rk (Submodule.map (e : ((Fin n → R) × (Fin m → R)) →ₗ[R] (Fin (n + m) → R))
            (Submodule.prod ⊥ Q)) := rdim_sup_le rk _ _
      _ = rdim rk P + rdim rk Q := by rw [hrdimA, hrdimB]
  have hv : rdim rk (Submodule.map (e : ((Fin n → R) × (Fin m → R)) →ₗ[R] (Fin (n + m) → R))
        (Submodule.prod (LinearMap.ker p) (LinearMap.ker q)))
      ≤ rdim rk (LinearMap.ker p) + rdim rk (LinearMap.ker q) := by
    rw [hmap1']
    calc rdim rk (Submodule.map (e : ((Fin n → R) × (Fin m → R)) →ₗ[R] (Fin (n + m) → R))
            (Submodule.prod (LinearMap.ker p) ⊥)
          ⊔ Submodule.map (e : ((Fin n → R) × (Fin m → R)) →ₗ[R] (Fin (n + m) → R))
            (Submodule.prod ⊥ (LinearMap.ker q)))
        ≤ rdim rk (Submodule.map (e : ((Fin n → R) × (Fin m → R)) →ₗ[R] (Fin (n + m) → R))
            (Submodule.prod (LinearMap.ker p) ⊥))
          + rdim rk (Submodule.map (e : ((Fin n → R) × (Fin m → R)) →ₗ[R] (Fin (n + m) → R))
            (Submodule.prod ⊥ (LinearMap.ker q))) := rdim_sup_le rk _ _
      _ = rdim rk (LinearMap.ker p) + rdim rk (LinearMap.ker q) := by rw [hrdimA', hrdimB']
  have hXY : rdim rk P + rdim rk Q + (rdim rk (LinearMap.ker p) + rdim rk (LinearMap.ker q))
      = ((n + m : ℕ) : ℝ) := by
    have hcast : ((n + m : ℕ) : ℝ) = (n : ℝ) + (m : ℝ) := by push_cast; ring
    linarith [hsumP, hsumQ]
  rw [hP, hQ]
  linarith [huv, hu, hv, hXY]

theorem rdim_prod_add {R : Type u} [Ring R] [VonNeumannRegularRing R] (rk : SylvesterRank R)
    {n m : ℕ} (e : ((Fin n → R) × (Fin m → R)) ≃ₗ[R] (Fin (n + m) → R))
    (P : Submodule R (Fin n → R)) (Q : Submodule R (Fin m → R)) :
    rdim rk (Submodule.map (e : ((Fin n → R) × (Fin m → R)) →ₗ[R] (Fin (n + m) → R))
      (Submodule.prod P Q))
      = rdim rk P + rdim rk Q := by
  refine le_antisymm ?_ ?_
  · rw [rdim_eq_sSup_span rk (Submodule.map
      (e : ((Fin n → R) × (Fin m → R)) →ₗ[R] (Fin (n + m) → R)) (Submodule.prod P Q))]
    refine csSup_le ?_ ?_
    · exact ⟨_, ⟨0, (fun i : Fin 0 => 0), (fun i => Fin.elim0 i), rfl⟩⟩
    · rintro x ⟨k, v, hv, rfl⟩
      have hmem : ∀ i : Fin k, ∃ a ∈ P, ∃ b ∈ Q,
          (e : ((Fin n → R) × (Fin m → R)) →ₗ[R] (Fin (n + m) → R)) (a, b) = v i := by
        intro i
        have hi := hv i
        rw [Submodule.mem_map] at hi
        obtain ⟨y, hy, hval⟩ := hi
        rw [Submodule.mem_prod] at hy
        exact ⟨y.1, hy.1, y.2, hy.2, hval⟩
      choose a ha b hb hab using hmem
      calc rdim rk (Submodule.span R (Set.range v))
          ≤ rdim rk (Submodule.map (e : ((Fin n → R) × (Fin m → R)) →ₗ[R] (Fin (n + m) → R))
              (Submodule.prod (Submodule.span R (Set.range a)) (Submodule.span R (Set.range b)))) := by
            refine rdim_mono rk ?_
            refine Submodule.span_le.mpr ?_
            rintro y ⟨i, rfl⟩
            exact ⟨(a i, b i), Submodule.mem_prod.mpr
              ⟨Submodule.subset_span ⟨i, rfl⟩, Submodule.subset_span ⟨i, rfl⟩⟩, hab i⟩
        _ = rdim rk (Submodule.span R (Set.range a))
              + rdim rk (Submodule.span R (Set.range b)) := rdim_prod_add_finSpan rk e a b
        _ ≤ rdim rk P + rdim rk Q := add_le_add
              (rdim_mono rk (Submodule.span_le.mpr (Set.range_subset_iff.mpr ha)))
              (rdim_mono rk (Submodule.span_le.mpr (Set.range_subset_iff.mpr hb)))
  · rw [rdim_eq_sSup_span rk P, rdim_eq_sSup_span rk Q]
    have hPne : ({x : ℝ | ∃ (k : ℕ) (v : Fin k → (Fin n → R)),
        (∀ i, v i ∈ P) ∧ x = rdim rk (Submodule.span R (Set.range v))} : Set ℝ).Nonempty :=
      ⟨_, ⟨0, (fun i : Fin 0 => 0), (fun i => Fin.elim0 i), rfl⟩⟩
    have hQne : ({x : ℝ | ∃ (k : ℕ) (v : Fin k → (Fin m → R)),
        (∀ i, v i ∈ Q) ∧ x = rdim rk (Submodule.span R (Set.range v))} : Set ℝ).Nonempty :=
      ⟨_, ⟨0, (fun i : Fin 0 => 0), (fun i => Fin.elim0 i), rfl⟩⟩
    have hPbdd : BddAbove {x : ℝ | ∃ (k : ℕ) (v : Fin k → (Fin n → R)),
        (∀ i, v i ∈ P) ∧ x = rdim rk (Submodule.span R (Set.range v))} :=
      ⟨rdim rk P, by
        rintro x ⟨k, v, hv, rfl⟩
        exact rdim_mono rk (Submodule.span_le.mpr (Set.range_subset_iff.mpr hv))⟩
    have hQbdd : BddAbove {x : ℝ | ∃ (k : ℕ) (v : Fin k → (Fin m → R)),
        (∀ i, v i ∈ Q) ∧ x = rdim rk (Submodule.span R (Set.range v))} :=
      ⟨rdim rk Q, by
        rintro x ⟨k, v, hv, rfl⟩
        exact rdim_mono rk (Submodule.span_le.mpr (Set.range_subset_iff.mpr hv))⟩
    rw [← csSup_add hPne hPbdd hQne hQbdd]
    refine csSup_le ?_ ?_
    · obtain ⟨a, ha⟩ := hPne
      obtain ⟨b, hb⟩ := hQne
      exact ⟨a + b, a, ha, b, hb, rfl⟩
    · rintro x ⟨aa, haa, bb, hbb, rfl⟩
      obtain ⟨ka, va, hva, rfl⟩ := haa
      obtain ⟨kb, vb, hvb, rfl⟩ := hbb
      refine le_trans (le_of_eq (rdim_prod_add_finSpan rk e va vb).symm) ?_
      exact rdim_mono rk (Submodule.map_mono (Submodule.prod_mono
        (Submodule.span_le.mpr (Set.range_subset_iff.mpr hva))
        (Submodule.span_le.mpr (Set.range_subset_iff.mpr hvb))))
end Work.ORHughesFree.NaturalExtension
