import Mathlib
import Submission.Work.WilE7.Defs

set_option autoImplicit false
noncomputable section
open Classical
namespace Work.WilE7
open WilkiesDesign WilkiesDesign.E

/-!
  `star_proj`: the class of `*`-sets (Binyamini–Novikov–Zak, area E) is closed under
  dropping coordinates, with the format and the degree unchanged.

  The content is the observation that a `StarPiece` in `n + M` variables whose
  semi-Pfaffian part lives in `(n + M) + m` can be *re-indexed* so that it becomes a
  `StarPiece` in `n` variables whose semi-Pfaffian part lives in `n + (m + M)`; the
  connected component is transported by the homeomorphism which permutes the
  coordinates, and the projection is then computed by `projFirst` composition.
-/

/-! ## The coordinate homeomorphism induced by a reindexing -/

/-- `y ↦ y ∘ e`, as a homeomorphism `(Fin K → ℝ) ≃ₜ (Fin k → ℝ)`. -/
def pullHomeo {k K : ℕ} (e : Fin k ≃ Fin K) : (Fin K → ℝ) ≃ₜ (Fin k → ℝ) where
  toFun y := fun i => y (e i)
  invFun x := fun j => x (e.symm j)
  left_inv y := by funext j; simp
  right_inv x := by funext i; simp
  continuous_toFun := continuous_pi fun i => continuous_apply (e i)
  continuous_invFun := continuous_pi fun j => continuous_apply (e.symm j)

theorem pullHomeo_apply {k K : ℕ} (e : Fin k ≃ Fin K) (y : Fin K → ℝ) :
    pullHomeo e y = fun i => y (e i) := rfl

theorem pullHomeo_symm_apply {k K : ℕ} (e : Fin k ≃ Fin K) (x : Fin k → ℝ) :
    (pullHomeo e).symm x = fun j => x (e.symm j) := rfl

/-- The value preserving equivalence `Fin ((n+M)+m) ≃ Fin (n+(m+M))`. -/
def spEquiv (n M m : ℕ) : Fin ((n + M) + m) ≃ Fin (n + (m + M)) :=
  finEquiv (by omega)

@[simp] theorem spEquiv_apply_val {n M m : ℕ} (i : Fin ((n + M) + m)) :
    ((spEquiv n M m) i).val = i.val := rfl

@[simp] theorem spEquiv_symm_apply_val {n M m : ℕ} (j : Fin (n + (m + M))) :
    ((spEquiv n M m).symm j).val = j.val := rfl

/-! ## Reindexing: evaluation of the chain and of the basic sets -/

theorem sp_reindex_ell {k K r : ℕ} (e : Fin k ≃ Fin K) (c : EAChain k r) (j : Fin r)
    (y : Fin K → ℝ) :
    (EAChain.reindex e c).ell j y = c.ell j (fun i => y (e i)) := by
  have h : (∑ i : Fin K, c.a j (e.symm i) * y i)
      = ∑ i : Fin k, c.a j i * y (e i) := by
    rw [← Equiv.sum_comp e.symm (fun i : Fin k => c.a j i * y (e i))]
    apply Finset.sum_congr rfl
    intro i _
    rw [Equiv.apply_symm_apply]
  simp only [EAChain.ell, EAChain.reindex]
  rw [h]

theorem sp_reindex_eval {k K r : ℕ} (e : Fin k ≃ Fin K) (c : EAChain k r) (Q : EAPoly k r)
    (y : Fin K → ℝ) :
    eaEval (EAChain.reindex e c) (EAPoly.reindex e Q) y = eaEval c Q (fun i => y (e i)) := by
  have hfun : (Sum.elim y (fun j => Real.exp ((EAChain.reindex e c).ell j y))) ∘ Sum.map e id
      = Sum.elim (fun i => y (e i)) (fun j => Real.exp (c.ell j (fun i => y (e i)))) := by
    funext s
    rcases s with i | j
    · rfl
    · simp only [Function.comp_apply, Sum.map_inr, Sum.elim_inr]
      rw [sp_reindex_ell]
      rfl
  simp only [eaEval, EAPoly.reindex, MvPolynomial.eval_rename, hfun]

theorem sp_reindex_holds {k K : ℕ} (e : Fin k ≃ Fin K) (r : ℕ) (c : EAChain k r)
    (B : Basic k r) (y : Fin K → ℝ) :
    (Basic.reindex e B).holds (EAChain.reindex e c) y ↔ B.holds c (fun i => y (e i)) := by
  have hfg : (Basic.reindex e B).eqs = B.eqs.map (EAPoly.reindex e) := rfl
  have hpg : (Basic.reindex e B).pos = B.pos.map (EAPoly.reindex e) := rfl
  constructor
  · intro h
    refine ⟨fun f hf => ?_, fun g hg => ?_⟩
    · have hh := h.1 (EAPoly.reindex e f) (by rw [hfg]; exact List.mem_map_of_mem hf)
      simpa only [sp_reindex_eval] using hh
    · have hh := h.2 (EAPoly.reindex e g) (by rw [hpg]; exact List.mem_map_of_mem hg)
      simpa only [sp_reindex_eval] using hh
  · intro h
    refine ⟨fun f hf => ?_, fun g hg => ?_⟩
    · rw [hfg] at hf
      obtain ⟨f0, hf0, rfl⟩ := List.mem_map.mp hf
      simpa only [sp_reindex_eval] using h.1 f0 hf0
    · rw [hpg] at hg
      obtain ⟨g0, hg0, rfl⟩ := List.mem_map.mp hg
      simpa only [sp_reindex_eval] using h.2 g0 hg0

/-- The set of a reindexed semi-Pfaffian set: pointwise form. -/
theorem sp_reindex_mem {k K : ℕ} (e : Fin k ≃ Fin K) (X : SemiPf k) (y : Fin K → ℝ) :
    y ∈ (SemiPf.reindex e X).set ↔ (fun i => y (e i)) ∈ X.set := by
  simp only [SemiPf.set, Set.mem_ofPred_eq, cubeC]
  constructor
  · rintro ⟨hcube, B, hB, hBh⟩
    obtain ⟨B0, hB0, rfl⟩ := List.mem_map.mp hB
    exact ⟨fun i => hcube (e i), B0, hB0, (sp_reindex_holds e X.r X.c B0 y).mp hBh⟩
  · rintro ⟨hcube, B0, hB0, hBh⟩
    refine ⟨fun j => ?_, Basic.reindex e B0, List.mem_map_of_mem hB0,
      (sp_reindex_holds e X.r X.c B0 y).mpr hBh⟩
    have hh2 := hcube (e.symm j)
    rwa [Equiv.apply_symm_apply] at hh2

theorem sp_reindex_set {k K : ℕ} (e : Fin k ≃ Fin K) (X : SemiPf k) :
    (SemiPf.reindex e X).set = {y | (fun i => y (e i)) ∈ X.set} :=
  Set.ext fun y => sp_reindex_mem e X y

theorem sp_reindex_set_pull {k K : ℕ} (e : Fin k ≃ Fin K) (X : SemiPf k) :
    (SemiPf.reindex e X).set = (pullHomeo e) ⁻¹' X.set := by
  ext y
  rw [Set.mem_preimage]
  exact sp_reindex_mem e X y

/-! ## Reindexing: degree -/

theorem sp_atomDeg_reindex {k K r : ℕ} (e : Fin k ≃ Fin K) (Q : EAPoly k r) :
    atomDeg (EAPoly.reindex e Q) = atomDeg Q := by
  have hgf : (Sum.map e.symm id : Fin K ⊕ Fin r → Fin k ⊕ Fin r) ∘ (Sum.map e id) = id := by
    funext s
    rcases s with a | b <;> simp
  have h2 : MvPolynomial.rename (Sum.map e.symm id) (MvPolynomial.rename (Sum.map e id) Q)
      = Q := by
    rw [MvPolynomial.rename_rename, hgf]
    first | rfl | simp [MvPolynomial.rename_id]
  have hle := MvPolynomial.totalDegree_rename_le (Sum.map e.symm id)
    (MvPolynomial.rename (Sum.map e id) Q)
  rw [h2] at hle
  have hmain : (MvPolynomial.rename (Sum.map e id) Q).totalDegree = Q.totalDegree :=
    le_antisymm (MvPolynomial.totalDegree_rename_le (Sum.map e id) Q) hle
  simp only [atomDeg, EAPoly.reindex, hmain]

theorem sp_basic_deg_reindex {k K r : ℕ} (e : Fin k ≃ Fin K) (B : Basic k r) :
    (Basic.reindex e B).deg = B.deg := by
  have h : ∀ l : List (EAPoly k r),
      (l.map (EAPoly.reindex e)).map atomDeg = l.map atomDeg := by
    intro l
    induction l with
    | nil => rfl
    | cons a t ih => simp [ih, sp_atomDeg_reindex e a]
  simp only [Basic.deg, Basic.reindex, List.map_append]
  rw [h B.eqs, h B.pos]

theorem sp_reindex_deg {k K : ℕ} (e : Fin k ≃ Fin K) (X : SemiPf k) :
    (SemiPf.reindex e X).deg = X.deg := by
  have h : ∀ l : List (Basic k X.r),
      (l.map (Basic.reindex e)).map Basic.deg = l.map Basic.deg := by
    intro l
    induction l with
    | nil => rfl
    | cons a t ih => simp [ih, sp_basic_deg_reindex e a]
  simp only [SemiPf.deg, SemiPf.reindex]
  rw [h X.basics]

/-! ## Reindexing: connected components -/

theorem sp_reindex_component {k K : ℕ} (e : Fin k ≃ Fin K) (X : SemiPf k) (p : Fin k → ℝ) :
    connectedComponentIn (SemiPf.reindex e X).set ((pullHomeo e).symm p)
      = (pullHomeo e) ⁻¹' connectedComponentIn X.set p := by
  have hset : (SemiPf.reindex e X).set = (pullHomeo e) ⁻¹' X.set := sp_reindex_set_pull e X
  by_cases hp : p ∈ X.set
  · have hx : (pullHomeo e).symm p ∈ (SemiPf.reindex e X).set := by
      rw [hset, Set.mem_preimage, Homeomorph.apply_symm_apply]
      exact hp
    have key := Homeomorph.image_connectedComponentIn (pullHomeo e) hx
    have h1 : (pullHomeo e) '' (SemiPf.reindex e X).set = X.set := by
      rw [hset]
      exact Set.image_preimage_eq _ (Homeomorph.surjective _)
    have h2 : (pullHomeo e) ((pullHomeo e).symm p) = p := Homeomorph.apply_symm_apply _ _
    rw [h1, h2] at key
    rw [← key, Homeomorph.preimage_image]
  · have hx : (pullHomeo e).symm p ∉ (SemiPf.reindex e X).set := by
      rw [hset, Set.mem_preimage, Homeomorph.apply_symm_apply]
      exact hp
    rw [connectedComponentIn_eq_empty hx, connectedComponentIn_eq_empty hp, Set.preimage_empty]

/-! ## Shifting a `*`-piece -/

/-- View a `*`-piece in `n + M` variables as one in `n` variables: the fibre dimension
grows by `M` and the coordinates are re-indexed along `Fin ((n+M)+m) ≃ Fin (n+(m+M))`. -/
def sp_shift {n M : ℕ} (P : StarPiece (n + M)) : StarPiece n :=
  ⟨P.m + M, SemiPf.reindex (spEquiv n M P.m) P.X,
   (pullHomeo (spEquiv n M P.m)).symm P.p⟩

theorem sp_shift_fmt {n M : ℕ} (P : StarPiece (n + M)) :
    (sp_shift P).X.fmt = P.X.fmt := by
  simp only [sp_shift, SemiPf.fmt, SemiPf.reindex]
  omega

theorem sp_shift_deg {n M : ℕ} (P : StarPiece (n + M)) :
    (sp_shift P).X.deg = P.X.deg := by
  simp only [sp_shift]
  exact sp_reindex_deg (spEquiv n M P.m) P.X

/-- The projection of the first `n` coordinates commutes with the change of coordinates. -/
theorem sp_projFirst_push {n m M : ℕ} (x : Fin ((n + M) + m) → ℝ) :
    projFirst n (m + M) (fun i => x ((spEquiv n M m).symm i))
      = projFirst n M (projFirst (n + M) m x) := by
  funext i
  simp only [projFirst]
  exact congrArg x (Fin.ext (by simp))

theorem sp_preimage_pull {k K : ℕ} (e : Fin k ≃ Fin K) (C : Set (Fin k → ℝ)) :
    (pullHomeo e) ⁻¹' C = (pullHomeo e).symm '' C := by
  ext y
  simp only [Set.mem_preimage, Set.mem_image]
  constructor
  · intro hy
    exact ⟨(pullHomeo e) y, hy, Homeomorph.symm_apply_apply (pullHomeo e) y⟩
  · rintro ⟨x, hx, rfl⟩
    simpa using hx

theorem sp_shift_set {n M : ℕ} (P : StarPiece (n + M)) :
    (sp_shift P).set = projFirst n M '' P.set := by
  have hc := sp_reindex_component (spEquiv n M P.m) P.X P.p
  have hfun : (fun x : Fin ((n + M) + P.m) → ℝ =>
        projFirst n (P.m + M) ((pullHomeo (spEquiv n M P.m)).symm x))
      = fun x => projFirst n M (projFirst (n + M) P.m x) := by
    funext x
    exact sp_projFirst_push x
  show projFirst n (P.m + M) ''
        connectedComponentIn (SemiPf.reindex (spEquiv n M P.m) P.X).set
          ((pullHomeo (spEquiv n M P.m)).symm P.p)
      = projFirst n M '' projFirst (n + M) P.m '' connectedComponentIn P.X.set P.p
  rw [hc, sp_preimage_pull]
  simp only [Set.image_image, hfun]

/-! ## Assembling -/

theorem sp_iUnion_map {α β γ : Type*} (f : α → β) (L : List α) (g : β → Set γ) :
    (⋃ b ∈ L.map f, g b) = ⋃ a ∈ L, g (f a) := by
  apply le_antisymm
  · intro z hz
    simp only [Set.mem_iUnion, List.mem_map, exists_prop] at hz ⊢
    obtain ⟨b, ⟨a, ha, rfl⟩, hz⟩ := hz
    exact ⟨a, ha, hz⟩
  · intro z hz
    simp only [Set.mem_iUnion, List.mem_map, exists_prop] at hz ⊢
    obtain ⟨a, ha, hz⟩ := hz
    exact ⟨f a, ⟨a, ha, rfl⟩, hz⟩

theorem sp_star_proj {n M F D : ℕ} {Z : Set (Fin (n + M) → ℝ)}
    (h : Star F D (n + M) Z) : Star F D n (projFirst n M '' Z) := by
  obtain ⟨L, hZ, hfmt, hdeg⟩ := h
  refine ⟨L.map sp_shift, ?_, ?_, ?_⟩
  · rw [hZ]
    simp only [Set.image_iUnion, sp_iUnion_map, sp_shift_set]
  · intro Q hQ
    rw [List.mem_map] at hQ
    obtain ⟨P, hP, rfl⟩ := hQ
    rw [sp_shift_fmt]
    exact hfmt P hP
  · have hsum : (L.map sp_shift).map (fun Q => Q.X.deg) = L.map (fun P => P.X.deg) := by
      rw [List.map_map]
      apply List.map_congr_left
      intro P _
      exact sp_shift_deg P
    rw [hsum]
    exact hdeg

/-! ## The statement -/

theorem star_proj :
    (∀ {N F D : ℕ} {Z : Set (Fin (N + 1) → ℝ)},
        WilkiesDesign.E.Star F D (N + 1) Z → WilkiesDesign.E.Star F D N (Fin.init '' Z)) ∧
    (∀ {n M F D : ℕ} {Z : Set (Fin (n + M) → ℝ)},
        WilkiesDesign.E.Star F D (n + M) Z →
        WilkiesDesign.E.Star F D n (WilkiesDesign.E.projFirst n M '' Z)) := by
  constructor
  · intro N F D Z h
    have hf : (Fin.init : (Fin (N + 1) → ℝ) → (Fin N → ℝ)) = projFirst N 1 := by
      funext z i
      rw [projFirst]
      rfl
    rw [hf]
    exact sp_star_proj h
  · intro n M F D Z h
    exact sp_star_proj h

end Work.WilE7
