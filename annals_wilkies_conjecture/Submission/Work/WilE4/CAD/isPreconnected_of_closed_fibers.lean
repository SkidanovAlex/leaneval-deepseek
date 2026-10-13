/-
  WilE4 / CAD — preconnectedness of a closed family with preconnected, locally bounded fibres.

  If `C ⊆ ℝ^k` is preconnected and `X ⊆ ℝ^k × ℝ` is closed with `X ⊆ C × ℝ`, with every fibre
  `{t | (x,t) ∈ X}` (`x ∈ C`) nonempty and preconnected, and with every fibre *locally bounded*
  near each `x ∈ C`, then `X` is preconnected.

  The two ingredients are

  * for a closed `A ⊆ X` the projection `Prod.fst '' A` is closed *relative to* `C`: a limit of
    first coordinates can be lifted because the second coordinates stay in a fixed compact interval
    (`exists_snd_of_mem_closure_fst`);
  * every fibre over `C` lies entirely in one of the two parts of any closed 2-cover of `X`
    (`isPreconnected_iff_subset_of_disjoint_closed` applied in the fibre).

  Then the two parts `Prod.fst '' (X ∩ T₁)` and `Prod.fst '' (X ∩ T₂)` are relatively clopen and
  disjoint, so preconnectedness of `C` forces one of them to be empty, and the corresponding
  `X ∩ Tᵢ` is empty as well.
-/
import Mathlib

open Filter Topology
open scoped Topology

namespace Work.WilE4.CAD

/-- **Lifting a limit through locally bounded fibres.** If `A` is a closed subset of `X`, the
`X`-fibres are bounded by `B` on a neighbourhood of `x`, and `x` is a limit point of the projection
`Prod.fst '' A`, then there is a point of `A` above `x`. -/
lemma exists_snd_of_mem_closure_fst {k : ℕ} {A X : Set ((Fin k → ℝ) × ℝ)}
    (hA : IsClosed A) (hAX : A ⊆ X) {x : Fin k → ℝ} {B : ℝ}
    (hbdd : ∀ᶠ x' in nhds x, ∀ t : ℝ, (x', t) ∈ X → |t| ≤ B)
    (hx : x ∈ closure (Prod.fst '' A)) : ∃ t : ℝ, (x, t) ∈ A := by
  classical
  -- an open neighbourhood of `x` on which the fibres are bounded by `B`
  obtain ⟨U, hUsub, hUopen, hxU⟩ := mem_nhds_iff.mp hbdd
  -- a sequence of first coordinates in the projection of `A`, converging to `x`
  obtain ⟨v, hvA, hvx⟩ := mem_closure_iff_seq_limit.mp hx
  have hcho : ∀ n, ∃ t, (v n, t) ∈ A := fun n => by
    obtain ⟨p, hpA, hp⟩ := (Set.mem_image Prod.fst A (v n)).mp (hvA n)
    exact ⟨p.2, by rwa [← hp]⟩
  choose t ht using hcho
  have hev : ∀ᶠ n in atTop, v n ∈ U := hvx.eventually (hUopen.mem_nhds hxU)
  obtain ⟨N, hN⟩ := Filter.eventually_atTop.mp hev
  -- from the `N`-th term on, all second coordinates lie in `Icc (-B) B`
  have hbound : ∀ n, |t (n + N)| ≤ B := by
    intro n
    have h1 : v (n + N) ∈ U := hN (n + N) (Nat.le_add_left N n)
    exact hUsub h1 (t (n + N)) (hAX (ht (n + N)))
  -- Bolzano–Weierstrass on the bounded tail
  obtain ⟨a, ha, φ, hφmono, hφtend⟩ :=
    (isCompact_Icc (a := -B) (b := B)).tendsto_subseq (x := fun n => t (n + N))
      (fun n => abs_le.mp (hbound n))
  have hv' : Tendsto (fun m => v (φ m + N)) atTop (𝓝 x) :=
    ((Filter.tendsto_add_atTop_iff_nat N).mpr hvx).comp hφmono.tendsto_atTop
  have hprod := hv'.prodMk_nhds hφtend
  exact ⟨a, hA.mem_of_tendsto hprod (Eventually.of_forall (fun n => ht (φ n + N)))⟩

theorem isPreconnected_of_closed_fibers {k : ℕ} {C : Set (Fin k → ℝ)} (hC : IsPreconnected C)
    {X : Set ((Fin k → ℝ) × ℝ)} (hcl : IsClosed X) (hsub : ∀ p ∈ X, p.1 ∈ C)
    (hint : ∀ x ∈ C, IsPreconnected {t : ℝ | (x, t) ∈ X})
    (hne : ∀ x ∈ C, ∃ t : ℝ, (x, t) ∈ X)
    (hbd : ∀ x ∈ C, ∃ B : ℝ,
      Filter.Eventually (fun x' => ∀ t : ℝ, (x', t) ∈ X → |t| ≤ B) (nhds x)) :
    IsPreconnected X := by
  classical
  rw [isPreconnected_iff_subset_of_disjoint_closed]
  intro T₁ T₂ hT₁ hT₂ hcover hdisj
  have hAcl : IsClosed (X ∩ T₁) := hcl.inter hT₁
  have hBcl : IsClosed (X ∩ T₂) := hcl.inter hT₂
  have hAX : X ∩ T₁ ⊆ X := Set.inter_subset_left
  have hBX : X ∩ T₂ ⊆ X := Set.inter_subset_left
  -- Every fibre over `C` lies entirely in `T₁` or entirely in `T₂`: the two parts are closed and
  -- disjoint in the (preconnected, nonempty) fibre.
  have hfiber : ∀ x ∈ C,
      (∀ t, (x, t) ∈ X → (x, t) ∈ T₁) ∨ (∀ t, (x, t) ∈ X → (x, t) ∈ T₂) := by
    intro x hxC
    have h1 : IsClosed {t : ℝ | (x, t) ∈ T₁} :=
      hT₁.preimage (continuous_const.prodMk continuous_id)
    have h2 : IsClosed {t : ℝ | (x, t) ∈ T₂} :=
      hT₂.preimage (continuous_const.prodMk continuous_id)
    have hcov' : {t : ℝ | (x, t) ∈ X} ⊆ {t | (x, t) ∈ T₁} ∪ {t | (x, t) ∈ T₂} := by
      intro t ht; simpa using hcover ht
    have hdisj' : {t : ℝ | (x, t) ∈ X} ∩ ({t | (x, t) ∈ T₁} ∩ {t | (x, t) ∈ T₂}) = ∅ := by
      rw [Set.eq_empty_iff_forall_notMem]
      rintro t ⟨htX, ht1, ht2⟩
      exact (Set.eq_empty_iff_forall_notMem.mp hdisj) (x, t) ⟨htX, ht1, ht2⟩
    rcases (isPreconnected_iff_subset_of_disjoint_closed.mp (hint x hxC))
        {t : ℝ | (x, t) ∈ T₁} {t : ℝ | (x, t) ∈ T₂} h1 h2 hcov' hdisj' with h | h
    · exact Or.inl fun t ht => h ht
    · exact Or.inr fun t ht => h ht
  -- For closed `A ⊆ X`, the projection of `A` is closed in the subspace `C`.
  have hkey : ∀ {A' : Set ((Fin k → ℝ) × ℝ)}, IsClosed A' → A' ⊆ X →
      C ∩ closure (Prod.fst '' A') = Prod.fst '' A' := by
    intro A' hA' hA'X
    apply Set.Subset.antisymm
    · rintro x ⟨hxC, hxcl⟩
      obtain ⟨B, hB⟩ := hbd x hxC
      obtain ⟨t, ht⟩ := exists_snd_of_mem_closure_fst hA' hA'X hB hxcl
      exact ⟨(x, t), ht, rfl⟩
    · rintro x ⟨p, hp, rfl⟩
      exact ⟨hsub p (hA'X hp), subset_closure ⟨p, hp, rfl⟩⟩
  have hkey₁ := hkey hAcl hAX
  have hkey₂ := hkey hBcl hBX
  have hC₁sub : Prod.fst '' (X ∩ T₁) ⊆ C := by
    rintro x ⟨p, hp, rfl⟩; exact hsub p hp.1
  have hC₂sub : Prod.fst '' (X ∩ T₂) ⊆ C := by
    rintro x ⟨p, hp, rfl⟩; exact hsub p hp.1
  -- the two projections cover `C` ...
  have hcover12 : C ⊆ Prod.fst '' (X ∩ T₁) ∪ Prod.fst '' (X ∩ T₂) := by
    intro x hxC
    rcases hfiber x hxC with h | h
    · obtain ⟨t, ht⟩ := hne x hxC
      exact Or.inl ⟨(x, t), ⟨ht, h t ht⟩, rfl⟩
    · obtain ⟨t, ht⟩ := hne x hxC
      exact Or.inr ⟨(x, t), ⟨ht, h t ht⟩, rfl⟩
  -- ... and they are disjoint.
  have hdisj12 : C ∩ (Prod.fst '' (X ∩ T₁) ∩ Prod.fst '' (X ∩ T₂)) = ∅ := by
    rw [Set.eq_empty_iff_forall_notMem]
    rintro x ⟨hxC, ⟨p, hp, hp1⟩, ⟨q, hq, hq1⟩⟩
    have hpe : (x, p.2) = p := by rw [← hp1]
    have hqe : (x, q.2) = q := by rw [← hq1]
    rcases hfiber x hxC with h | h
    · refine (Set.eq_empty_iff_forall_notMem.mp hdisj) q ⟨hq.1, ?_, hq.2⟩
      have hmem : (x, q.2) ∈ X := by rw [hqe]; exact hq.1
      have hT : (x, q.2) ∈ T₁ := h q.2 hmem
      rwa [hqe] at hT
    · refine (Set.eq_empty_iff_forall_notMem.mp hdisj) p ⟨hp.1, hp.2, ?_⟩
      have hmem : (x, p.2) ∈ X := by rw [hpe]; exact hp.1
      have hT : (x, p.2) ∈ T₂ := h p.2 hmem
      rwa [hpe] at hT
  have hcov2 : C ⊆ closure (Prod.fst '' (X ∩ T₁)) ∪ closure (Prod.fst '' (X ∩ T₂)) := by
    intro x hx
    rcases hcover12 hx with h | h
    · exact Or.inl (subset_closure h)
    · exact Or.inr (subset_closure h)
  have hdisj2 :
      C ∩ (closure (Prod.fst '' (X ∩ T₁)) ∩ closure (Prod.fst '' (X ∩ T₂))) = ∅ := by
    rw [Set.eq_empty_iff_forall_notMem]
    rintro x ⟨hxC, hx1, hx2⟩
    have e1 : x ∈ Prod.fst '' (X ∩ T₁) := by rw [← hkey₁]; exact ⟨hxC, hx1⟩
    have e2 : x ∈ Prod.fst '' (X ∩ T₂) := by rw [← hkey₂]; exact ⟨hxC, hx2⟩
    exact (Set.eq_empty_iff_forall_notMem.mp hdisj12) x ⟨hxC, e1, e2⟩
  rcases (isPreconnected_iff_subset_of_disjoint_closed.mp hC)
      (closure (Prod.fst '' (X ∩ T₁))) (closure (Prod.fst '' (X ∩ T₂)))
      isClosed_closure isClosed_closure hcov2 hdisj2 with h | h
  · -- `C ⊆ closure (fst '' (X ∩ T₁))`, hence `X ∩ T₂ = ∅`
    have hC2empty : Prod.fst '' (X ∩ T₂) = ∅ := by
      rw [Set.eq_empty_iff_forall_notMem]
      intro x hx
      have hx1 : x ∈ Prod.fst '' (X ∩ T₁) := by
        rw [← hkey₁]; exact ⟨hC₂sub hx, h (hC₂sub hx)⟩
      exact (Set.eq_empty_iff_forall_notMem.mp hdisj12) x ⟨hC₂sub hx, hx1, hx⟩
    have hBempty : X ∩ T₂ = ∅ := by
      rw [Set.eq_empty_iff_forall_notMem]
      intro p hp
      exact (Set.eq_empty_iff_forall_notMem.mp hC2empty) p.1 ⟨p, hp, rfl⟩
    left
    intro p hp
    rcases hcover hp with hh | hh
    · exact hh
    · exact absurd ⟨hp, hh⟩ (Set.eq_empty_iff_forall_notMem.mp hBempty p)
  · -- `C ⊆ closure (fst '' (X ∩ T₂))`, hence `X ∩ T₁ = ∅`
    have hC1empty : Prod.fst '' (X ∩ T₁) = ∅ := by
      rw [Set.eq_empty_iff_forall_notMem]
      intro x hx
      have hx1 : x ∈ Prod.fst '' (X ∩ T₂) := by
        rw [← hkey₂]; exact ⟨hC₁sub hx, h (hC₁sub hx)⟩
      exact (Set.eq_empty_iff_forall_notMem.mp hdisj12) x ⟨hC₁sub hx, hx, hx1⟩
    have hAempty : X ∩ T₁ = ∅ := by
      rw [Set.eq_empty_iff_forall_notMem]
      intro p hp
      exact (Set.eq_empty_iff_forall_notMem.mp hC1empty) p.1 ⟨p, hp, rfl⟩
    right
    intro p hp
    rcases hcover hp with hh | hh
    · exact absurd ⟨hp, hh⟩ (Set.eq_empty_iff_forall_notMem.mp hAempty p)
    · exact hh

end Work.WilE4.CAD
