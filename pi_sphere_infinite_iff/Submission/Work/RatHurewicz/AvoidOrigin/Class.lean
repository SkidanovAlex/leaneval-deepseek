import Mathlib
import Submission.Work.RatHurewicz.AvoidOrigin.Transport

/-!
# The class of a point of a cell of the cycle model

This module describes the class of a point `Sum.inl ⟨i, x⟩` of `Raw D` (with `x` a point of the
standard simplex whose support `S` has at least three vertices) under the gluing relation
`modelRel D`: it is exactly the set of transports of `x` along the vertex maps of `ChainTrans`.
-/

open scoped Topology unitInterval

namespace Work.RatHurewicz

noncomputable section

variable {X : Type} [TopologicalSpace X] {x₀ : X} {n : ℕ}

/-! ## Elementary properties of the transport -/

/-- Transport along the identity is the identity. -/
theorem transportPt_id {S : Finset (Fin (n + 2))} (x : stdSimplex ℝ (Fin (n + 2)))
    (hx : ptSupport x = S) (h : Function.Injective (fun t : {t // t ∈ S} => t.1)) :
    transportPt x hx (fun t => t.1) h = x := by
  refine Subtype.ext (funext fun w => ?_)
  change (transportPt x hx (fun t => t.1) h : Fin (n + 2) → ℝ) w
    = (x : Fin (n + 2) → ℝ) w
  rw [transportPt_apply]
  by_cases hw : w ∈ S
  · rw [Finset.sum_eq_single ⟨w, hw⟩]
    · simp
    · intro t _ ht
      rw [if_neg (fun hc => ht (Subtype.ext hc))]
    · intro hmem; exact absurd (Finset.mem_univ _) hmem
  · have hz : (∑ t : {t // t ∈ S},
        if (↑t : Fin (n + 2)) = w then (x : Fin (n + 2) → ℝ) t else 0) = 0 :=
      Finset.sum_eq_zero fun t _ => by
        by_cases hc : (↑t : Fin (n + 2)) = w
        · exact absurd (hc ▸ t.2) hw
        · rw [if_neg hc]
    have hzero : (x : Fin (n + 2) → ℝ) w = 0 := not_not.mp fun hne =>
      hw (hx ▸ mem_ptSupport.mpr hne)
    rw [hz, ← hzero]

/-- The support of a transported point is the image of the support under the vertex map. -/
theorem transportPtSupp {S : Finset (Fin (n + 2))} (x : stdSimplex ℝ (Fin (n + 2)))
    (hx : ptSupport x = S) (τ : {t // t ∈ S} → Fin (n + 2)) (hτ : Function.Injective τ) :
    ptSupport (transportPt x hx τ hτ) = S.attach.image τ := by
  ext w
  rw [mem_ptSupport, Finset.mem_image]
  constructor
  · intro hw
    by_contra h
    push Not at h
    refine hw (Finset.sum_eq_zero fun t _ => ?_)
    rw [if_neg]
    exact h t (Finset.mem_attach S t)
  · rintro ⟨t, _, rfl⟩
    have hxne : (x : Fin (n + 2) → ℝ) t ≠ 0 := mem_ptSupport.mp (hx ▸ t.2)
    rw [transportPt_apply]
    have hle : (if τ t = τ t then (x : Fin (n + 2) → ℝ) t else 0)
        ≤ ∑ t' : {t // t ∈ S}, if τ t' = τ t then (x : Fin (n + 2) → ℝ) t' else 0 :=
      Finset.single_le_sum
        (f := fun t' : {t // t ∈ S} => if τ t' = τ t then (x : Fin (n + 2) → ℝ) t' else 0)
        (fun t' _ => by
          by_cases hc : τ t' = τ t
          · rw [if_pos hc]; exact x.2.1 t'
          · rw [if_neg hc]) (Finset.mem_univ t)
    rw [if_pos rfl] at hle
    exact ne_of_gt (lt_of_lt_of_le (lt_of_le_of_ne (x.2.1 t) (Ne.symm hxne)) hle)

/-- Every vertex map of a chain is strictly monotone. -/
theorem chainTransStrictMono (D : MData X n x₀) {i : D.Idx} {S : Finset (Fin (n + 2))}
    {j : D.Idx} {τ : {t // t ∈ S} → Fin (n + 2)} (h : ChainTrans D i S j τ) :
    StrictMono τ := by
  induction h with
  | refl => intro a b hab; exact hab
  | step hprev hp hface ih =>
      intro a b hab
      exact Fin.strictMono_succAbove _ (strictMono_invSuccAbove _ (hp a) (hp b) (ih hab))

/-- The coordinate of a `facept` at the vertex dropped by the face map is zero. -/
theorem facept_self_zero {m : ℕ} (p : Fin (m + 1)) (u : stdSimplex ℝ (Fin m)) :
    (facept m p u : Fin (m + 1) → ℝ) p = 0 := by
  rw [facept_apply]
  exact Finset.sum_eq_zero fun v hv =>
    absurd (Finset.mem_filter.mp hv).2 (Fin.succAbove_ne p v)

/-- **The coordinates of the inverse image of a point under a face map.** -/
theorem map_invSuccAbove_apply {m : ℕ} [NeZero m] {p : Fin (m + 1)}
    {z : stdSimplex ℝ (Fin (m + 1))} (hz : p ∉ rawSupp z) (v : Fin m) :
    ((stdSimplex.map (invSuccAbove p) z : stdSimplex ℝ (Fin m)) : Fin m → ℝ) v
      = (z : Fin (m + 1) → ℝ) (Fin.succAbove p v) := by
  rw [map_apply_eq_sum]
  rw [Finset.sum_eq_single (Fin.succAbove p v)]
  · intro w' hw' hne
    have h1 : w' = p := by
      by_contra hp'
      exact hne (by rw [← succAbove_invSuccAbove p hp', (Finset.mem_filter.mp hw').2])
    rw [h1]
    exact not_not.mp fun hone => hz (mem_rawSupp.mpr hone)
  · intro hmem
    exact absurd (Finset.mem_filter.mpr ⟨Finset.mem_univ (Fin.succAbove p v),
      invSuccAbove_succAbove p v⟩) hmem

/-- **The inverse of a face map, as an explicit point of the smaller simplex.** -/
theorem facept_map_invSuccAbove {m : ℕ} [NeZero m] {p : Fin (m + 1)}
    {z : stdSimplex ℝ (Fin (m + 1))} (hz : p ∉ rawSupp z) :
    facept m p (stdSimplex.map (invSuccAbove p) z) = z := by
  have hzp : (z : Fin (m + 1) → ℝ) p = 0 := not_not.mp fun hone => hz (mem_rawSupp.mpr hone)
  refine Subtype.ext (funext fun w => ?_)
  change (facept m p (stdSimplex.map (invSuccAbove p) z) : Fin (m + 1) → ℝ) w
    = (z : Fin (m + 1) → ℝ) w
  rw [facept_apply]
  rw [Finset.sum_congr rfl fun v _ => map_invSuccAbove_apply hz v]
  by_cases hw : w = p
  · rw [hw]
    rw [Finset.sum_eq_zero fun v hv =>
      absurd (Finset.mem_filter.mp hv).2 (Fin.succAbove_ne p v)]
    exact hzp.symm
  · have h1 : Fin.succAbove p (invSuccAbove p w) = w := succAbove_invSuccAbove p hw
    have hfil : Finset.univ.filter (fun v : Fin m => Fin.succAbove p v = w)
        = {invSuccAbove p w} := by
      ext v
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_singleton]
      exact ⟨fun h => by rw [← invSuccAbove_succAbove p v, h], fun h => by rw [h, h1]⟩
    rw [hfil, Finset.sum_singleton, h1]

/-- **Every point of a face is the image of a point of the smaller simplex under the face map.** -/
theorem exists_facept_eq {m : ℕ} [NeZero m] {p : Fin (m + 1)} {z : stdSimplex ℝ (Fin (m + 1))}
    (hz : p ∉ rawSupp z) : ∃ u : stdSimplex ℝ (Fin m), facept m p u = z :=
  ⟨_, facept_map_invSuccAbove hz⟩


/-- The predicate "the raw point is a transport of `x` along a chain". -/
def InClass (D : MData X n x₀) (i : D.Idx) (S : Finset (Fin (n + 2)))
    (x : stdSimplex ℝ (Fin (n + 2))) (hx : ptSupport x = S) (b : Raw D) : Prop :=
  ∃ (j : D.Idx) (τ : {t // t ∈ S} → Fin (n + 2)) (hτ : Function.Injective τ),
    ChainTrans D i S j τ ∧ b = Sum.inl ⟨j, transportPt x hx τ hτ⟩

/-- **Every chain relates the corresponding raw points.** -/
theorem chainTrans_class (D : MData X n x₀) {i : D.Idx} {S : Finset (Fin (n + 2))}
    {x : stdSimplex ℝ (Fin (n + 2))} (hx : ptSupport x = S) :
    ∀ {j : D.Idx} {τ : {t // t ∈ S} → Fin (n + 2)}, ChainTrans D i S j τ →
      ∀ hτ : Function.Injective τ,
        Relation.EqvGen (modelRel D) (Sum.inl ⟨i, x⟩) (Sum.inl ⟨j, transportPt x hx τ hτ⟩) := by
  intro j τ h
  refine ChainTrans.rec
    (motive := fun (j : D.Idx) (τ : {t // t ∈ S} → Fin (n + 2)) _ =>
      ∀ hτ : Function.Injective τ,
        Relation.EqvGen (modelRel D) (Sum.inl ⟨i, x⟩)
          (Sum.inl ⟨j, transportPt x hx τ hτ⟩)) ?_ ?_ h
  · intro hτ
    rw [transportPt_id x hx hτ]
    exact Relation.EqvGen.refl _
  · intro j τ l p q hprev hp hface ih hτnew
    have hτ : Function.Injective τ := (chainTransStrictMono D hprev).injective
    have hclass := ih hτ
    have hpraw : p ∉ rawSupp (transportPt x hx τ hτ) := by
      rw [← ptSupport_eq_rawSupp, transportPtSupp x hx τ hτ]
      intro hmem
      obtain ⟨t, -, ht⟩ := Finset.mem_image.mp hmem
      exact hp t ht
    have hrel : modelRel D
        (Sum.inl ⟨j, facept (n + 1) p
          (stdSimplex.map (invSuccAbove p) (transportPt x hx τ hτ))⟩)
        (Sum.inl ⟨l, facept (n + 1) q
          (stdSimplex.map (invSuccAbove p) (transportPt x hx τ hτ))⟩) :=
      Or.inl ⟨j, l, p, q, _, rfl, rfl, hface⟩
    rw [facept_map_invSuccAbove hpraw] at hrel
    rw [step_transportPt hx hτ hp (facept_map_invSuccAbove hpraw) hτnew] at hrel
    refine Relation.EqvGen.trans (x := (Sum.inl ⟨i, x⟩ : Raw D))
      (y := (Sum.inl ⟨j, transportPt x hx τ hτ⟩ : Raw D))
      (z := (Sum.inl ⟨l, transportPt x hx
        (fun t => Fin.succAbove q (invSuccAbove p (τ t))) hτnew⟩ : Raw D)) ?_ ?_
    · exact hclass
    · exact Relation.EqvGen.rel _ _ hrel

/-- **The class of a point of a cell.** -/
theorem chainTrans (D : MData X n x₀) (i : D.Idx) (S : Finset (Fin (n + 2)))
    (hS : 2 < S.card) (x : stdSimplex ℝ (Fin (n + 2))) (hx : ptSupport x = S) (b : Raw D) :
    Relation.EqvGen (modelRel D) (Sum.inl ⟨i, x⟩) b ↔ InClass D i S x hx b := by
  have hQ : ∀ a b : Raw D, modelRel D a b → (InClass D i S x hx a ↔ InClass D i S x hx b) := by
    intro a b hab
    constructor
    · rintro ⟨j, τ, hτ, hCT, rfl⟩
      rcases hab with ⟨j', l, p, q, u, ha, hb, hface⟩ | ⟨j', ha, hb⟩ | ⟨j', l, ha, hb⟩
      · have h1 : (⟨j, transportPt x hx τ hτ⟩ :
            Σ _ : D.Idx, stdSimplex ℝ (Fin (n + 2))) = ⟨j', facept (n + 1) p u⟩ :=
          Sum.inl.inj ha
        have hj : j = j' := congrArg Sigma.fst h1
        have hu : transportPt x hx τ hτ = facept (n + 1) p u := congrArg Sigma.snd h1
        have hp : ∀ t, τ t ≠ p := by
          intro t ht
          have hmem : p ∈ S.attach.image τ :=
            Finset.mem_image.mpr ⟨t, Finset.mem_attach S t, ht⟩
          rw [← transportPtSupp x hx τ hτ, hu, mem_ptSupport] at hmem
          exact hmem (facept_self_zero p u)
        have hτnew : Function.Injective (fun t => Fin.succAbove q (invSuccAbove p (τ t))) := by
          intro t t' htt'
          exact hτ (invSuccAbove_injOn p (hp t) (hp t')
            (Fin.succAbove_right_injective htt'))
        have hstep := step_transportPt hx hτ hp hu.symm hτnew
        rw [← hj] at hface
        exact ⟨l, _, hτnew, ChainTrans.step hCT hp hface,
          hb.trans (congrArg (fun z : stdSimplex ℝ (Fin (n + 2)) =>
            (Sum.inl ⟨l, z⟩ : Raw D)) hstep)⟩
      · exfalso
        have h1 : (⟨j, transportPt x hx τ hτ⟩ :
            Σ _ : D.Idx, stdSimplex ℝ (Fin (n + 2))) =
              ⟨j', stdSimplex.vertex (0 : Fin (n + 2))⟩ := Sum.inl.inj ha
        have hu : transportPt x hx τ hτ = stdSimplex.vertex (0 : Fin (n + 2)) :=
          congrArg Sigma.snd h1
        have hc1 : (ptSupport (transportPt x hx τ hτ)).card = S.card := by
          rw [transportPtSupp x hx τ hτ, Finset.card_image_of_injective _ hτ,
            Finset.card_attach]
        have hc2 : (ptSupport (transportPt x hx τ hτ)).card = 1 := by
          rw [hu, ptSupport_vertex, Finset.card_singleton]
        omega
      · exact absurd ha Sum.inl_ne_inr
    · rintro ⟨j, τ, hτ, hCT, rfl⟩
      rcases hab with ⟨j', l, p, q, u, ha, hb, hface⟩ | ⟨j', ha, hb⟩ | ⟨j', l, ha, hb⟩
      · have h1 : (⟨j, transportPt x hx τ hτ⟩ :
            Σ _ : D.Idx, stdSimplex ℝ (Fin (n + 2))) = ⟨l, facept (n + 1) q u⟩ :=
          Sum.inl.inj hb
        have hj : j = l := congrArg Sigma.fst h1
        have hu : transportPt x hx τ hτ = facept (n + 1) q u := congrArg Sigma.snd h1
        have hq : ∀ t, τ t ≠ q := by
          intro t ht
          have hmem : q ∈ S.attach.image τ :=
            Finset.mem_image.mpr ⟨t, Finset.mem_attach S t, ht⟩
          rw [← transportPtSupp x hx τ hτ, hu, mem_ptSupport] at hmem
          exact hmem (facept_self_zero q u)
        have hτnew : Function.Injective (fun t => Fin.succAbove p (invSuccAbove q (τ t))) := by
          intro t t' htt'
          exact hτ (invSuccAbove_injOn q (hq t) (hq t')
            (Fin.succAbove_right_injective htt'))
        have hstep := step_transportPt hx hτ hq hu.symm hτnew
        rw [← hj] at hface
        exact ⟨j', _, hτnew, ChainTrans.step hCT hq hface.symm,
          ha.trans (congrArg (fun z : stdSimplex ℝ (Fin (n + 2)) =>
            (Sum.inl ⟨j', z⟩ : Raw D)) hstep)⟩
      · exfalso
        exact Sum.inl_ne_inr hb
      · exfalso
        exact Sum.inl_ne_inr hb
  have hmain : ∀ a b : Raw D, Relation.EqvGen (modelRel D) a b →
      (InClass D i S x hx a ↔ InClass D i S x hx b) := by
    intro a b hab
    induction hab with
    | rel a b h => exact hQ a b h
    | refl a => exact Iff.rfl
    | symm a b h ih => exact ih.symm
    | trans a b c h1 h2 ih1 ih2 => exact ih1.trans ih2
  constructor
  · intro hb
    refine (hmain _ _ hb).mp ⟨i, (fun t => t.1), (fun a b h => Subtype.ext h),
      ChainTrans.refl, ?_⟩
    rw [transportPt_id x hx (fun a b h => Subtype.ext h)]
  · rintro ⟨j, τ, hτ, hCT, rfl⟩
    exact chainTrans_class D hx hCT hτ

end

end Work.RatHurewicz
