import Submission.Work.ConeSwitch.MathlibNoHG
import Submission.Work.Deep.Nibble.AuxDefs

set_option autoImplicit false
open scoped BigOperators

namespace Work.Deep.Nibble

open ErdosFaberLovaszConjecture

theorem exp_two_le_iff : (2:ℝ) ≤ Real.exp 2 := by
  have h := Real.add_one_le_exp (2:ℝ)
  linarith

theorem auxFam_card_le {D n X FV FE : ℝ} (hD0 : 0 ≤ D) (hDn : D ≤ n) (hnX : n ≤ X)
    (he : Real.exp 2 ≤ n) (hFV0 : 0 ≤ FV) (hFV : FV ≤ n^(Real.log n))
    (hFE : FE ≤ n^(Real.log n)) :
    D * FV + FE ≤ X^(2*Real.log X) := by
  have hn1 : (1:ℝ) ≤ n := le_trans (le_trans (by norm_num : (1:ℝ) ≤ 2) exp_two_le_iff) he
  have hn0 : 0 < n := lt_of_lt_of_le one_pos hn1
  have hn2 : (2:ℝ) ≤ n := le_trans exp_two_le_iff he
  have hlog2 : 2 ≤ Real.log n := (Real.le_log_iff_exp_le hn0).mpr he
  have hlogn0 : 0 ≤ Real.log n := by linarith
  have hnpow0 : 0 ≤ n^(Real.log n) := Real.rpow_nonneg (le_of_lt hn0) _
  have hnpow1 : (1:ℝ) ≤ n^(Real.log n) := Real.one_le_rpow hn1 hlogn0
  -- `n + 1 ≤ n^(log n)`
  have hsqu : n^(2:ℝ) ≤ n^(Real.log n) := Real.rpow_le_rpow_of_exponent_le hn1 hlog2
  have hsqu2 : n^(2:ℝ) = n^2 := Real.rpow_natCast n 2
  have hn1le : n + 1 ≤ n^(2:ℝ) := by rw [hsqu2]; nlinarith
  have hkey : n + 1 ≤ n^(Real.log n) := le_trans hn1le hsqu
  -- main chain
  have hstep1 : D * FV ≤ n * n^(Real.log n) :=
    mul_le_mul hDn hFV hFV0 (le_of_lt hn0)
  have hstep2 : D * FV + FE ≤ n * n^(Real.log n) + n^(Real.log n) := add_le_add hstep1 hFE
  have hstep3 : n * n^(Real.log n) + n^(Real.log n) = (n+1) * n^(Real.log n) := by ring
  have hstep4 : (n+1) * n^(Real.log n) ≤ n^(Real.log n) * n^(Real.log n) :=
    mul_le_mul_of_nonneg_right hkey hnpow0
  have hpow : n^(Real.log n) * n^(Real.log n) = n^(2 * Real.log n) := by
    rw [← Real.rpow_add hn0]; ring_nf
  have hstep5 : n^(2 * Real.log n) ≤ X^(2 * Real.log n) :=
    Real.rpow_le_rpow (le_of_lt hn0) hnX (by linarith)
  have hstep6 : X^(2 * Real.log n) ≤ X^(2 * Real.log X) := by
    have hlogX : Real.log n ≤ Real.log X := Real.log_le_log hn0 hnX
    exact Real.rpow_le_rpow_of_exponent_le (le_trans hn1 hnX) (by linarith)
  calc D * FV + FE ≤ n * n^(Real.log n) + n^(Real.log n) := hstep2
    _ = (n+1) * n^(Real.log n) := hstep3
    _ ≤ n^(Real.log n) * n^(Real.log n) := hstep4
    _ = n^(2 * Real.log n) := hpow
    _ ≤ X^(2 * Real.log n) := hstep5
    _ ≤ X^(2 * Real.log X) := hstep6

/-- Unfolding `psiOf` at a `κ (Sum.inl e)`-edge recovers `e`. -/
theorem psiOf_inl_apply {n r : ℕ} {D' C : ℝ} {𝓗' : MultiHypergraph n} (W : EmbedWitness n r D' C 𝓗')
    (e : Set (Fin n)) (he : e ∈ 𝓗'.edges)
    (hmeet : ((W.κ (Sum.inl ⟨e, he⟩) : Set (Fin W.M)) ∩
      W.ι '' {v : Fin n | 0 < 𝓗'.deg v}).Nonempty) :
    psiOf W ⟨(W.κ (Sum.inl ⟨e, he⟩) : Set (Fin W.M)), (W.κ (Sum.inl ⟨e, he⟩)).2.1, hmeet⟩ = e := by
  have h1 : (⟨(W.κ (Sum.inl ⟨e, he⟩) : Set (Fin W.M)), (W.κ (Sum.inl ⟨e, he⟩)).2.1, hmeet⟩ :
      {x : Set (Fin W.M) // x ∈ W.𝓖 ∧ (x ∩ W.ι '' {v : Fin n | 0 < 𝓗'.deg v}).Nonempty})
      = W.κ (Sum.inl ⟨e, he⟩) := Subtype.ext rfl
  unfold psiOf
  rw [h1, Equiv.symm_apply_apply]

/-- If `psiOf W f = e` with `e` a proper edge of `𝓗'`, then `f` is the
`κ`-preimage of `e`. -/
theorem subtype_eq_kappa_inl {n r : ℕ} {D' C : ℝ} {𝓗' : MultiHypergraph n}
    (W : EmbedWitness n r D' C 𝓗')
    (f : {x : Set (Fin W.M) // x ∈ W.𝓖 ∧ (x ∩ W.ι '' {v : Fin n | 0 < 𝓗'.deg v}).Nonempty})
    {e : Set (Fin n)} (he : e ∈ 𝓗'.edges) (h2 : 2 ≤ edgeSize e)
    (h : psiOf W f = e) :
    f = W.κ (Sum.inl ⟨e, he⟩) := by
  have hy : W.κ.symm f = Sum.inl ⟨e, he⟩ := by
    unfold psiOf at h
    split at h
    · next q hq =>
      rw [hq]
      exact congrArg Sum.inl (Subtype.ext h)
    · next q hq =>
      exfalso
      have : edgeSize e = 1 := by rw [← h, edgeSize_eq_ncard, Set.ncard_singleton]
      omega
  rw [← Equiv.apply_symm_apply W.κ f, hy]

theorem ncard_psiInvSet_le {n r : ℕ} {D' C : ℝ} {𝓗' : MultiHypergraph n}
    (W : EmbedWitness n r D' C 𝓗') {F : Set (Set (Fin n))}
    (hlin : 𝓗'.IsLinear) (hF : ∀ e ∈ F, e ∈ 𝓗'.edges) :
    (psiInvSet W F).ncard ≤ F.ncard := by
  classical
  refine Nat.card_le_card_of_injective
    (fun f : {x // x ∈ psiInvSet W F} =>
      (⟨psiOf W ⟨f.1, f.2.choose, (f.2.choose_spec).choose⟩,
        (f.2.choose_spec).choose_spec⟩ : {e // e ∈ F})) ?_
  intro f g heq
  have hval : psiOf W ⟨f.1, f.2.choose, (f.2.choose_spec).choose⟩
      = psiOf W ⟨g.1, g.2.choose, (g.2.choose_spec).choose⟩ := congrArg Subtype.val heq
  have hE1 : psiOf W ⟨f.1, f.2.choose, (f.2.choose_spec).choose⟩ ∈ 𝓗'.edges :=
    hF _ (f.2.choose_spec).choose_spec
  have h2 : 2 ≤ edgeSize (psiOf W ⟨f.1, f.2.choose, (f.2.choose_spec).choose⟩) := hlin.1 _ hE1
  have hf1 : f.1 = (W.κ (Sum.inl ⟨_, hE1⟩) : Set (Fin W.M)) :=
    congrArg Subtype.val
      (subtype_eq_kappa_inl W ⟨f.1, f.2.choose, (f.2.choose_spec).choose⟩ hE1 h2 rfl)
  have hg1 : g.1 = (W.κ (Sum.inl ⟨_, hE1⟩) : Set (Fin W.M)) :=
    congrArg Subtype.val
      (subtype_eq_kappa_inl W ⟨g.1, g.2.choose, (g.2.choose_spec).choose⟩ hE1 h2 (by rw [hval]))
  exact Subtype.ext (hf1.trans hg1.symm)

theorem embed_C_bound {C₀ β D n : ℝ} (hβ : 0 < β) (hC₀ : 0 < C₀)
    (hn : (C₀/(2*β))^2 + 1 ≤ n) (hD : n^(1/2 : ℝ) ≤ D) : C₀ ≤ 2*β*D := by
  have h2β : 0 < 2*β := by linarith
  have hx0 : 0 ≤ C₀/(2*β) := le_of_lt (div_pos hC₀ h2β)
  have hnpos : 0 < n := by nlinarith [sq_nonneg (C₀/(2*β))]
  have hx : C₀/(2*β) ≤ n^(1/2 : ℝ) := by
    have h := (Real.le_sqrt hx0 (le_of_lt hnpos)).mpr (by nlinarith [hn] : (C₀/(2*β))^2 ≤ n)
    rwa [Real.sqrt_eq_rpow] at h
  calc C₀ = 2*β * (C₀/(2*β)) := by field_simp
    _ ≤ 2*β * n^(1/2 : ℝ) := by nlinarith [hx, h2β]
    _ ≤ 2*β * D := by nlinarith [hD, h2β]

theorem cardX_rpow_le_D {X D n : ℝ} (hX0 : 0 ≤ X) (hX : X ≤ n^7) (hn1 : 1 ≤ n)
    (hD : n^(1/2 : ℝ) ≤ D) : X^(1/100 : ℝ) ≤ D := by
  have hn0 : 0 < n := lt_of_lt_of_le one_pos hn1
  have h1 : X^(1/100 : ℝ) ≤ (n^7)^(1/100 : ℝ) :=
    Real.rpow_le_rpow hX0 hX (by norm_num)
  have h2 : (n^7)^(1/100 : ℝ) = n^(7/100 : ℝ) := by
    rw [← Real.rpow_natCast n 7, ← Real.rpow_mul (le_of_lt hn0)]
    norm_num
  rw [h2] at h1
  have h3 : n^(7/100 : ℝ) ≤ n^(1/2 : ℝ) :=
    Real.rpow_le_rpow_of_exponent_le hn1 (by norm_num)
  linarith

theorem rpow_inv_bound {κ D n : ℝ} (hκ0 : 0 < κ) (hκ1 : κ ≤ 1)
    (hn : (30/κ)^40 ≤ n) (hDlo : n^(1/2 : ℝ) ≤ D) :
    D^(1/20 : ℝ) ≤ (κ/20)*D := by
  have h20pos : (0:ℝ) < 30/κ := div_pos (by norm_num) hκ0
  have h20 : (1:ℝ) ≤ 30/κ := by rw [one_le_div hκ0]; linarith
  have hn1 : (1:ℝ) ≤ n := le_trans (one_le_pow₀ h20) hn
  have hn0 : 0 < n := lt_of_lt_of_le one_pos hn1
  have hDhalf : (1:ℝ) ≤ n^(1/2 : ℝ) :=
    Real.one_le_rpow hn1 (show (0:ℝ) ≤ 1/2 by norm_num)
  have hDpos : 0 < D := lt_of_lt_of_le one_pos (le_trans hDhalf hDlo)
  have hbase : ((30/κ)^40)^(1/2 : ℝ) = (30/κ)^20 := by
    rw [← Real.rpow_natCast (30/κ) 40, ← Real.rpow_mul (le_of_lt h20pos)]
    have h40 : ((40:ℕ):ℝ) * (1/2) = ((20:ℕ):ℝ) := by norm_num
    rw [h40, Real.rpow_natCast]
  have hD20 : (30/κ)^20 ≤ D := by
    have h := Real.rpow_le_rpow (le_of_lt (pow_pos h20pos 40)) hn
      (show (0:ℝ) ≤ 1/2 by norm_num)
    rw [hbase] at h
    linarith
  set t : ℝ := D^(1/20 : ℝ) with ht
  have ht0 : 0 ≤ t := by positivity
  have ht20 : 30/κ ≤ t := by
    have hbase2 : ((30/κ)^20)^(1/20 : ℝ) = (30/κ) := by
      rw [← Real.rpow_natCast (30/κ) 20, ← Real.rpow_mul (le_of_lt h20pos)]
      have h20' : ((20:ℕ):ℝ) * (1/20) = ((1:ℕ):ℝ) := by norm_num
      rw [h20', Real.rpow_natCast, pow_one]
    have h := Real.rpow_le_rpow (le_of_lt (pow_pos h20pos 20)) hD20
      (show (0:ℝ) ≤ 1/20 by norm_num)
    rw [hbase2] at h
    rw [ht]; exact h
  have ht20eq : t^20 = D := by
    rw [ht, ← Real.rpow_natCast (D^(1/20:ℝ)) 20, ← Real.rpow_mul (le_of_lt hDpos)]
    have h20'' : (1/20:ℝ) * ((20:ℕ):ℝ) = ((1:ℕ):ℝ) := by norm_num
    rw [h20'', Real.rpow_natCast, pow_one]
  have ht19 : 20/κ ≤ t^19 := by
    have h1 : (30/κ)^19 ≤ t^19 := pow_le_pow_left₀ (le_of_lt h20pos) ht20 19
    have h2 : (30/κ : ℝ) ≤ (30/κ)^19 := by
      have h := Real.rpow_le_rpow_of_exponent_le h20 (show (1:ℝ) ≤ (19:ℝ) by norm_num)
      simpa using h
    have h3 : (20:ℝ)/κ ≤ 30/κ := by rw [div_le_div_iff_of_pos_right hκ0]; norm_num
    linarith
  have hκ5pos : (0:ℝ) < κ/20 := div_pos hκ0 (by norm_num)
  have key : (1:ℝ) ≤ (κ/20) * t^19 := by
    have h := mul_le_mul_of_nonneg_left ht19 (le_of_lt hκ5pos)
    have h' : (κ/20) * (20/κ) = 1 := by field_simp
    linarith [h, h']
  calc D^(1/20 : ℝ) = t := by rw [ht]
    _ = t * 1 := by ring
    _ ≤ t * ((κ/20) * t^19) := mul_le_mul_of_nonneg_left key ht0
    _ = (κ/20) * D := by rw [show t * ((κ/20) * t^19) = (κ/20) * t^20 by ring, ht20eq]


/-- The labelling `(f, i) ↦ auxEdge f i` is injective on the edges of `𝓗_aux`. -/
theorem auxEdge_inj {n M D : ℕ} {𝓖 : ErdosFaberLovaszConjecture.Hypergraph (Fin M)}
    {ι : Fin n ↪ Fin M} {Mfam : Fin D → Set (Set (Fin n))} {f f' : Set (Fin M)}
    (hf : f ∈ 𝓖) (hf' : f' ∈ 𝓖)
    {i i' : Fin D} (hd : f ∩ ι '' ErdosFaberLovaszConjecture.famVert (Mfam i) = ∅)
    (hd' : f' ∩ ι '' ErdosFaberLovaszConjecture.famVert (Mfam i') = ∅) (hne : f.Nonempty)
    (h : auxEdge n M D 𝓖 ι Mfam f i = auxEdge n M D 𝓖 ι Mfam f' i') :
    f = f' ∧ i = i' := by
  have h1 : f = f' := by
    have hmem : auxVInl n M D 𝓖 ι Mfam f hf ∈ auxEdge n M D 𝓖 ι Mfam f' i' := by
      rw [← h]; exact (auxVInl_mem_auxEdge hf i).mpr rfl
    rw [val_mem_auxEdge, auxVInl_val] at hmem
    rcases hmem with hh | ⟨v, hh, _⟩
    · exact Sum.inl.inj hh
    · exact absurd hh Sum.inl_ne_inr
  subst h1
  have h2 : i = i' := by
    obtain ⟨v, hv⟩ := hne
    have hv' : v ∉ ι '' ErdosFaberLovaszConjecture.famVert (Mfam i) := by
      intro hvmem
      have hv'' : v ∈ f ∩ ι '' ErdosFaberLovaszConjecture.famVert (Mfam i) := ⟨hv, hvmem⟩
      rw [hd] at hv''; exact hv''
    have hmem : auxVInr n M D 𝓖 ι Mfam i v hv' ∈ auxEdge n M D 𝓖 ι Mfam f i' := by
      rw [← h]; exact Or.inr ⟨v, rfl, hv⟩
    rw [val_mem_auxEdge, auxVInr_val] at hmem
    rcases hmem with hh | ⟨w, hh, _⟩
    · exact absurd hh Sum.inr_ne_inl
    · exact congrArg Prod.fst (Sum.inr.inj hh)
  exact ⟨rfl, h2⟩

/-- The cardinality of a finite union is at most the sum of the cardinalities. -/
theorem ncard_iUnion_le {ι : Type*} [Fintype ι] {α : Type*} [Finite α] (s : ι → Set α) :
    (⋃ i, s i).ncard ≤ ∑ i, (s i).ncard := by
  have h : Nat.card ↥(⋃ i, s i) ≤ Nat.card (Σ i, ↥(s i)) :=
    Nat.card_le_card_of_surjective
      (fun p : (Σ i, ↥(s i)) => (⟨p.2.1, Set.mem_iUnion.mpr ⟨p.1, p.2.2⟩⟩ : ↥(⋃ i, s i)))
      (by
        rintro ⟨x, hx⟩
        rw [Set.mem_iUnion] at hx
        obtain ⟨i, hi⟩ := hx
        exact ⟨⟨i, ⟨x, hi⟩⟩, Subtype.ext rfl⟩)
  rw [Nat.card_sigma] at h
  simp only [Nat.card_coe_set_eq] at h
  exact h

end Work.Deep.Nibble
