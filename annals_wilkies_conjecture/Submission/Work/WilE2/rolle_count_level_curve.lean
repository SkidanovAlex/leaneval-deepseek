import Mathlib
import Submission.Work.WilE2.Rolle
import Submission.Work.WilE2.integral_curve_unique_global
import Submission.Work.WilE2.exists_level_points_periodic
import Submission.Work.WilE2.deriv_alternates_at_zeros
import Submission.Work.WilE2.exists_fundamental_period
import Submission.Work.WilE2.exists_pos_lt_abs_of_isCompact
import Submission.Work.WilE2.finite_zeros_of_simple

set_option autoImplicit false
set_option maxHeartbeats 1000000

noncomputable section

namespace Work.WilE2

open Set

/-! ## Helper lemmas (mine) -/

theorem periodic_add_nat_mul {α : Type*} {f : ℝ → α} {T : ℝ} (hper : ∀ t, f (t + T) = f t)
    (n : ℕ) (t : ℝ) : f (t + n * T) = f t := by
  induction n with
  | zero => simp
  | succ k ih =>
      rw [Nat.cast_succ]
      have h1 : t + ((k : ℝ) + 1) * T = (t + k * T) + T := by ring
      rw [h1, hper, ih]

theorem periodic_sub_nat_mul {α : Type*} {f : ℝ → α} {T : ℝ} (hper : ∀ t, f (t + T) = f t)
    (n : ℕ) (t : ℝ) : f (t - n * T) = f t := by
  induction n with
  | zero => simp
  | succ k ih =>
      rw [Nat.cast_succ]
      have h1 : t - ((k : ℝ) + 1) * T = (t - k * T) - T := by ring
      rw [h1]
      have h2 := hper ((t - k * T) - T)
      rw [show (t - k * T) - T + T = t - k * T by ring] at h2
      rw [← h2, ih]

theorem periodic_add_int_mul {α : Type*} {f : ℝ → α} {T : ℝ} (hper : ∀ t, f (t + T) = f t)
    (n : ℤ) (t : ℝ) : f (t + (n : ℝ) * T) = f t := by
  rcases Int.eq_nat_or_neg n with ⟨k, hk | hk⟩
  · subst hk
    simpa using periodic_add_nat_mul hper k t
  · subst hk
    have hc : (((-(k : ℤ) : ℤ)) : ℝ) = -(k : ℝ) := by simp
    rw [hc]
    have h1 : t + -(k : ℝ) * T = t - k * T := by ring
    rw [h1]
    exact periodic_sub_nat_mul hper k t

theorem exists_mem_Ico_of_periodic {α : Type*} {f : ℝ → α} {T : ℝ} (hT : 0 < T)
    (hper : ∀ t, f (t + T) = f t) (t : ℝ) : ∃ r ∈ Set.Ico 0 T, f r = f t := by
  refine ⟨t - (⌊t / T⌋ : ℝ) * T, ⟨?_, ?_⟩, ?_⟩
  · have h1 : ((⌊t / T⌋ : ℤ) : ℝ) ≤ t / T := Int.floor_le _
    have h2 : ((⌊t / T⌋ : ℤ) : ℝ) * T ≤ t := by
      have h3 := mul_le_mul_of_nonneg_right h1 (le_of_lt hT)
      rwa [div_mul_cancel₀ t (ne_of_gt hT)] at h3
    linarith
  · have h1 : t / T < ((⌊t / T⌋ : ℤ) : ℝ) + 1 := Int.lt_floor_add_one _
    have h3 := mul_lt_mul_of_pos_right h1 hT
    rw [div_mul_cancel₀ t (ne_of_gt hT)] at h3
    linarith
  · have h1 : t - (⌊t / T⌋ : ℝ) * T = t + ((-(⌊t / T⌋) : ℤ) : ℝ) * T := by
      push_cast; ring
    rw [h1]
    exact periodic_add_int_mul hper (-(⌊t / T⌋)) t

theorem hasDerivAt_comp_curve {m : ℕ} {g : (Fin m → ℝ) → ℝ} (hg : ContDiff ℝ 1 g)
    {X : (Fin m → ℝ) → (Fin m → ℝ)} {γ : ℝ → (Fin m → ℝ)}
    (hγ : ∀ t, HasDerivAt γ (X (γ t)) t) (t : ℝ) :
    HasDerivAt (fun s => g (γ s)) (fderiv ℝ g (γ t) (X (γ t))) t := by
  have hgd : HasFDerivAt g (fderiv ℝ g (γ t)) (γ t) :=
    (hg.differentiable (by norm_num)).differentiableAt.hasFDerivAt
  simpa only [Function.comp_def] using hgd.comp_hasDerivAt t (hγ t)

/-! ## The per-component counting lemma -/

theorem level_curve_component_count {m : ℕ} (V : (Fin m → ℝ) → (Fin (m - 1) → ℝ))
    (X : (Fin m → ℝ) → (Fin m → ℝ)) (g ψ : (Fin m → ℝ) → ℝ)
    (hV : ContDiff ℝ 1 V) (hX : ContDiff ℝ 1 X) (hg : ContDiff ℝ 1 g) (hψc : Continuous ψ)
    (hX0 : ∀ z, V z = 0 → X z ≠ 0)
    (hsweep : ∀ z, V z = 0 → ∃ (T : ℝ) (γ : ℝ → Fin m → ℝ), 0 < T ∧ γ 0 = z ∧
        (∀ t, HasDerivAt γ (X (γ t)) t) ∧ (∀ t, γ (t + T) = γ t) ∧
        Set.range γ = connectedComponentIn {z | V z = 0} z)
    (hpsi : ∀ z, V z = 0 → g z = 0 → ψ z = fderiv ℝ g z (X z))
    (hnd : ∀ z, V z = 0 → g z = 0 → fderiv ℝ g z (X z) ≠ 0)
    (δ : ℝ) (hδpos : 0 < δ) (hδlt : ∀ z, V z = 0 → g z = 0 → δ < |ψ z|)
    (z₀ : Fin m → ℝ) (hz₀ : V z₀ = 0)
    (s : Finset (Fin m → ℝ))
    (hs : ∀ z ∈ s, V z = 0 ∧ g z = 0 ∧ z ∈ connectedComponentIn {z | V z = 0} z₀) :
    ∃ t : Finset (Fin m → ℝ), (∀ z ∈ t, V z = 0 ∧ ψ z = δ) ∧
      (∀ z ∈ t, z ∈ connectedComponentIn {z | V z = 0} z₀) ∧ s.card ≤ t.card := by
  classical
  set C : Set (Fin m → ℝ) := connectedComponentIn {z | V z = 0} z₀ with hCdef
  obtain ⟨T, γ, hT, hγ0, hder, hper, hrange⟩ := hsweep z₀ hz₀
  have hγcont : Continuous γ := continuous_iff_continuousAt.mpr (fun t => (hder t).continuousAt)
  have hγV : ∀ t, V (γ t) = 0 := by
    intro t
    have ht : γ t ∈ connectedComponentIn {z | V z = 0} z₀ := by
      rw [← hrange]; exact Set.mem_range_self t
    exact connectedComponentIn_subset ({z : Fin m → ℝ | V z = 0}) z₀ ht
  have hXne : ∀ t, X (γ t) ≠ 0 := fun t => hX0 _ (hγV t)
  obtain ⟨T₀, hT₀pos, hper₀, ⟨k, hkpos, hTk⟩, hinj⟩ :=
    exists_fundamental_period X hX γ hder hXne hT hper
  set φ : ℝ → ℝ := fun s => g (γ s) with hφdef
  have hφderiv : ∀ t, HasDerivAt φ (fderiv ℝ g (γ t) (X (γ t))) t :=
    fun t => hasDerivAt_comp_curve hg hder t
  have hφcont : Continuous φ := hg.continuous.comp hγcont
  have hφper : ∀ t, φ (t + T₀) = φ t := fun t => by simp only [hφdef, hper₀ t]
  set w : ℝ → ℝ := fun t => ψ (γ t) with hwdef
  have hwcont : Continuous w := hψc.comp hγcont
  have hwper : ∀ t, w (t + T₀) = w t := fun t => by simp only [hwdef, hper₀ t]
  have hsimple : ∀ u, φ u = 0 → ∃ c : ℝ, c ≠ 0 ∧ HasDerivAt φ c u := by
    intro u hu
    exact ⟨fderiv ℝ g (γ u) (X (γ u)), hnd (γ u) (hγV u) hu, hφderiv u⟩
  have hfin : Set.Finite {t : ℝ | 0 ≤ t ∧ t ≤ T₀ ∧ φ t = 0} :=
    finite_zeros_of_simple hφcont hsimple 0 T₀
  set Z : Finset ℝ := hfin.toFinset.filter (fun t => t < T₀) with hZdef
  have hZmem : ∀ t, t ∈ Z ↔ 0 ≤ t ∧ t < T₀ ∧ φ t = 0 := by
    intro t
    rw [hZdef, Finset.mem_filter, Set.Finite.mem_toFinset]
    constructor
    · rintro ⟨⟨h0, hle, hφ⟩, hlt⟩; exact ⟨h0, hlt, hφ⟩
    · rintro ⟨h0, hlt, hφ⟩; exact ⟨⟨h0, le_of_lt hlt, hφ⟩, hlt⟩
  -- every point of the component has a lift in the fundamental interval
  have hex : ∀ z ∈ s, ∃ r, r ∈ Z ∧ γ r = z := by
    intro z hz
    have hzR : z ∈ Set.range γ := by rw [hrange]; exact (hs z hz).2.2
    obtain ⟨t, ht⟩ := hzR
    obtain ⟨r, hrIco, hrγ⟩ := exists_mem_Ico_of_periodic hT₀pos hper₀ t
    refine ⟨r, ?_, ?_⟩
    · rw [hZmem]
      refine ⟨hrIco.1, hrIco.2, ?_⟩
      rw [hφdef]
      show g (γ r) = 0
      rw [hrγ, ht]
      exact (hs z hz).2.1
    · rw [hrγ, ht]
  let f : (Fin m → ℝ) → ℝ := fun z => if h : ∃ r, r ∈ Z ∧ γ r = z then h.choose else 0
  have hf : ∀ z ∈ s, f z ∈ Z ∧ γ (f z) = z := by
    intro z hz
    have h := hex z hz
    simp only [f, dif_pos h]
    exact h.choose_spec
  have hcardZ : s.card ≤ Z.card := by
    refine Finset.card_le_card_of_injOn f (fun z hz => (hf z hz).1) ?_
    intro a ha b hb hab
    have h1 := (hf a ha).2
    have h2 := (hf b hb).2
    calc a = γ (f a) := h1.symm
      _ = γ (f b) := by rw [hab]
      _ = b := h2
  rcases Nat.eq_zero_or_pos s.card with hs0 | hspos
  · exact ⟨∅, by simp, by simp, by simp [Finset.card_eq_zero.mp hs0]⟩
  have hp : 0 < Z.card := lt_of_lt_of_le hspos hcardZ
  let u : Fin Z.card → ℝ := Z.orderEmbOfFin rfl
  have hu_mono : StrictMono u := (Z.orderEmbOfFin rfl).strictMono
  have hu_mem : ∀ j, u j ∈ Z := fun j => Finset.orderEmbOfFin_mem Z rfl j
  have hu_range : Set.range u = (Z : Set ℝ) := Finset.range_orderEmbOfFin Z rfl
  have hroots : {t : ℝ | 0 ≤ t ∧ t < T₀ ∧ φ t = 0} = Set.range u := by
    rw [hu_range]
    ext t
    simp only [Finset.mem_coe]
    exact (hZmem t).symm
  have hdiff : ∀ j, DifferentiableAt ℝ φ (u j) := fun j => (hφderiv (u j)).differentiableAt
  have hne : ∀ j, deriv φ (u j) ≠ 0 := by
    intro j
    rw [(hφderiv (u j)).deriv]
    exact hnd (γ (u j)) (hγV (u j)) ((hZmem (u j)).mp (hu_mem j)).2.2
  have halt_deriv : ∀ j : Fin Z.card,
      deriv φ (u j) * deriv φ (u (cycSucc hp j)) < 0 :=
    deriv_alternates_at_zeros hT₀pos hφcont hφper hp u hu_mono hroots hdiff hne
  have hw_eq : ∀ j, w (u j) = deriv φ (u j) := by
    intro j
    rw [hwdef, (hφderiv (u j)).deriv]
    exact hpsi (γ (u j)) (hγV (u j)) ((hZmem (u j)).mp (hu_mem j)).2.2
  have habs : ∀ j, δ < |w (u j)| := by
    intro j
    show δ < |ψ (γ (u j))|
    exact hδlt (γ (u j)) (hγV (u j)) ((hZmem (u j)).mp (hu_mem j)).2.2
  have halt : ∀ j, w (u j) * w (u (cycSucc hp j)) < 0 := by
    intro j
    rw [hw_eq j, hw_eq (cycSucc hp j)]
    exact halt_deriv j
  have hhi_u : ∀ j, u j < u ⟨0, hp⟩ + T₀ := by
    intro j
    have h0 : 0 ≤ u ⟨0, hp⟩ := ((hZmem _).mp (hu_mem _)).1
    have h1 : u j < T₀ := ((hZmem _).mp (hu_mem j)).2.1
    linarith
  obtain ⟨S, hScard, hSδ, hSwin⟩ :=
    exists_level_points_periodic hT₀pos hδpos hwcont hwper hp u hu_mono hhi_u habs halt
  have hinjS : Set.InjOn γ ↑S := by
    intro a ha b hb hab
    by_contra hneab
    rcases lt_or_gt_of_ne hneab with hlt | hlt
    · have ha1 : u ⟨0, hp⟩ < a := (hSwin a ha).1
      have hb2 : b < u ⟨0, hp⟩ + T₀ := (hSwin b hb).2
      exact (ne_of_lt hlt) (hinj a b (by linarith) (by linarith) hab)
    · have hb1 : u ⟨0, hp⟩ < b := (hSwin b hb).1
      have ha2 : a < u ⟨0, hp⟩ + T₀ := (hSwin a ha).2
      exact (ne_of_lt hlt) (hinj b a (by linarith) (by linarith) hab.symm)
  refine ⟨S.image γ, ?_, ?_, ?_⟩
  · intro z hz
    obtain ⟨a, ha, rfl⟩ := Finset.mem_image.mp hz
    exact ⟨hγV a, hSδ a ha⟩
  · intro z hz
    obtain ⟨a, ha, rfl⟩ := Finset.mem_image.mp hz
    rw [hCdef, ← hrange]
    exact Set.mem_range_self a
  · rw [Finset.card_image_of_injOn hinjS]
    exact le_trans hcardZ hScard

/-! ## The main theorem -/

theorem rolle_count_level_curve {m : ℕ} (V : (Fin m → ℝ) → (Fin (m - 1) → ℝ))
    (X : (Fin m → ℝ) → (Fin m → ℝ)) (g ψ : (Fin m → ℝ) → ℝ)
    (hV : ContDiff ℝ 1 V) (hX : ContDiff ℝ 1 X) (hg : ContDiff ℝ 1 g) (hψc : Continuous ψ)
    (hC : IsCompact {z | V z = 0})
    (hX0 : ∀ z, V z = 0 → X z ≠ 0)
    (htan : ∀ z, V z = 0 → ∀ i, fderiv ℝ (fun w => V w i) z (X z) = 0)
    (hsweep : ∀ z, V z = 0 → ∃ (T : ℝ) (γ : ℝ → Fin m → ℝ), 0 < T ∧ γ 0 = z ∧
        (∀ t, HasDerivAt γ (X (γ t)) t) ∧ (∀ t, γ (t + T) = γ t) ∧
        Set.range γ = connectedComponentIn {z | V z = 0} z)
    (hpsi : ∀ z, V z = 0 → g z = 0 → ψ z = fderiv ℝ g z (X z))
    (hnd : ∀ z, V z = 0 → g z = 0 → fderiv ℝ g z (X z) ≠ 0) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ s : Finset (Fin m → ℝ), (∀ z ∈ s, V z = 0 ∧ g z = 0) →
      ∃ t : Finset (Fin m → ℝ), (∀ z ∈ t, V z = 0 ∧ ψ z = δ) ∧ s.card ≤ t.card := by
  classical
  have hKcompact : IsCompact {z : Fin m → ℝ | V z = 0 ∧ g z = 0} := by
    have heq : {z : Fin m → ℝ | V z = 0 ∧ g z = 0} = {z | V z = 0} ∩ g ⁻¹' {0} := by
      ext z; simp
    rw [heq]
    exact hC.inter_right (isClosed_singleton.preimage hg.continuous)
  have hψne : ∀ z ∈ {z : Fin m → ℝ | V z = 0 ∧ g z = 0}, ψ z ≠ 0 := by
    rintro z ⟨hzV, hzg⟩
    rw [hpsi z hzV hzg]
    exact hnd z hzV hzg
  obtain ⟨δ, hδpos, hδlt⟩ := exists_pos_lt_abs_of_isCompact hKcompact hψc hψne
  have hδlt' : ∀ z, V z = 0 → g z = 0 → δ < |ψ z| := fun z h1 h2 => hδlt z ⟨h1, h2⟩
  refine ⟨δ, hδpos, ?_⟩
  intro s hs
  let cf : (Fin m → ℝ) → Set (Fin m → ℝ) :=
    fun z => connectedComponentIn {z' | V z' = 0} z
  set sc : Finset (Set (Fin m → ℝ)) := s.image cf with hsc
  have hpiece : ∀ C ∈ sc, ∃ t : Finset (Fin m → ℝ),
      (∀ z ∈ t, V z = 0 ∧ ψ z = δ) ∧ (∀ z ∈ t, z ∈ C) ∧
      (s.filter (fun z => z ∈ C)).card ≤ t.card := by
    intro C hC
    obtain ⟨z₀, hz₀s, hz₀eq⟩ := Finset.mem_image.mp hC
    subst hz₀eq
    have hz₀V : V z₀ = 0 := (hs z₀ hz₀s).1
    have hsfil : ∀ z ∈ s.filter (fun z => z ∈ cf z₀),
        V z = 0 ∧ g z = 0 ∧ z ∈ connectedComponentIn {z' | V z' = 0} z₀ := by
      intro z hz
      rw [Finset.mem_filter] at hz
      exact ⟨(hs z hz.1).1, (hs z hz.1).2, hz.2⟩
    obtain ⟨t, ht1, ht2, ht3⟩ :=
      level_curve_component_count V X g ψ hV hX hg hψc hX0 hsweep hpsi hnd δ hδpos hδlt'
        z₀ hz₀V (s.filter (fun z => z ∈ cf z₀)) hsfil
    exact ⟨t, ht1, ht2, ht3⟩
  let piece : Set (Fin m → ℝ) → Finset (Fin m → ℝ) :=
    fun C => if h : C ∈ sc then (hpiece C h).choose else ∅
  have piece_spec : ∀ C ∈ sc, (∀ z ∈ piece C, V z = 0 ∧ ψ z = δ) ∧
      (∀ z ∈ piece C, z ∈ C) ∧ (s.filter (fun z => z ∈ C)).card ≤ (piece C).card := by
    intro C hC
    have h := (hpiece C hC).choose_spec
    have hpc : piece C = (hpiece C hC).choose := by
      simp only [piece]; exact dif_pos hC
    rw [hpc]
    exact h
  have hdisj : (sc : Set (Set (Fin m → ℝ))).PairwiseDisjoint piece := by
    intro A hA B hB hne
    change Disjoint (piece A) (piece B)
    rw [Finset.disjoint_left]
    intro z hzA hzB
    have hzA' : z ∈ A := (piece_spec A hA).2.1 z hzA
    have hzB' : z ∈ B := (piece_spec B hB).2.1 z hzB
    obtain ⟨a, ha, hAeq⟩ := Finset.mem_image.mp hA
    obtain ⟨b, hb, hBeq⟩ := Finset.mem_image.mp hB
    have hza : z ∈ cf a := hAeq ▸ hzA'
    have hzb : z ∈ cf b := hBeq ▸ hzB'
    refine hne ?_
    rw [← hAeq, ← hBeq]
    exact (connectedComponentIn_eq hza).trans (connectedComponentIn_eq hzb).symm
  refine ⟨sc.disjiUnion piece hdisj, ?_, ?_⟩
  · intro z hz
    obtain ⟨C, hC, hzC⟩ := Finset.mem_disjiUnion.mp hz
    exact (piece_spec C hC).1 z hzC
  · rw [Finset.card_disjiUnion]
    have hsum : (∑ C ∈ sc, (s.filter (fun z => z ∈ C)).card) = s.card := by
      have hfib := Finset.card_eq_sum_card_fiberwise (f := cf) (s := s) (t := sc)
        (fun z hz => Finset.mem_image_of_mem cf hz)
      rw [hfib]
      refine Finset.sum_congr rfl (fun C hC => ?_)
      congr 1
      ext z
      simp only [Finset.mem_filter]
      constructor
      · rintro ⟨hzs, hzC⟩
        obtain ⟨a, ha, hAeq⟩ := Finset.mem_image.mp hC
        have hza : z ∈ cf a := hAeq ▸ hzC
        exact ⟨hzs, hAeq ▸ (connectedComponentIn_eq hza).symm⟩
      · rintro ⟨hzs, hzf⟩
        exact ⟨hzs, hzf ▸ mem_connectedComponentIn (hs z hzs).1⟩
    calc s.card = ∑ C ∈ sc, (s.filter (fun z => z ∈ C)).card := hsum.symm
      _ ≤ ∑ C ∈ sc, (piece C).card := Finset.sum_le_sum (fun C hC => (piece_spec C hC).2.2)

end Work.WilE2
