import Mathlib

/-!
# Extracting an arc from a continuous map with interval fibres

If `g : ℝ → X` is continuous into a metric space, has interval fibres on `[0,1]`
(`g s = g u` with `s ≤ t ≤ u` forces `g t = g s`) and separates its endpoints (`g 0 ≠ g 1`), then
`g` can be reparametrised to a continuous injective map on `[0,1]` joining `g 0` to `g 1`.
-/

namespace Work.Topology.PeanoContinuum

open Set Metric Filter

variable {X : Type*} [MetricSpace X]

/-- The part of the fibre of `w` lying in `[0,1]`. -/
def fibre (g : ℝ → X) (w : X) : Set ℝ := g ⁻¹' {w} ∩ Set.Icc (0 : ℝ) 1

/-- `g` has interval fibres on `[0,1]`. -/
def IsFibreInterval (g : ℝ → X) : Prop :=
  ∀ ⦃s t u : ℝ⦄, s ∈ Set.Icc (0:ℝ) 1 → u ∈ Set.Icc (0:ℝ) 1 → g s = g u →
    s ≤ t → t ≤ u → g t = g s

/-- The left endpoint of the fibre of `w`. -/
noncomputable def L (g : ℝ → X) (w : X) : ℝ := sInf (fibre g w)

/-- The right endpoint of the fibre of `w`. -/
noncomputable def R (g : ℝ → X) (w : X) : ℝ := sSup (fibre g w)

/-- The set of values of `g` on `[0,1]`. -/
def A (g : ℝ → X) : Set X := g '' Set.Icc (0:ℝ) 1

/-- The set of values of `g` at rational times of `[0,1]`. -/
def Dset (g : ℝ → X) : Set X :=
  g '' {t : ℝ | t ∈ Set.Icc (0:ℝ) 1 ∧ ∃ q : ℚ, (q : ℝ) = t}

/-- The rational values other than the two endpoints. -/
def D0 (g : ℝ → X) : Set X := Dset g \ {g 0, g 1}

/-- The `L`-values of the rational values other than the endpoints. -/
def W (g : ℝ → X) : Set ℝ := L g '' D0 g

section Basic

variable {g : ℝ → X}

lemma isCompact_fibre (hg : Continuous g) (w : X) : IsCompact (fibre g w) := by
  rw [fibre, Set.inter_comm]
  exact isCompact_Icc.inter_right (isClosed_singleton.preimage hg)

lemma fibre_nonempty {w : X} (hw : w ∈ g '' Set.Icc (0:ℝ) 1) : (fibre g w).Nonempty := by
  obtain ⟨t, ht, rfl⟩ := hw
  exact ⟨t, rfl, ht⟩

lemma L_mem (hg : Continuous g) {w : X} (hw : w ∈ g '' Set.Icc (0:ℝ) 1) : L g w ∈ fibre g w :=
  (isCompact_fibre hg w).sInf_mem (fibre_nonempty hw)

lemma R_mem (hg : Continuous g) {w : X} (hw : w ∈ g '' Set.Icc (0:ℝ) 1) : R g w ∈ fibre g w :=
  (isCompact_fibre hg w).sSup_mem (fibre_nonempty hw)

lemma g_L (hg : Continuous g) {w : X} (hw : w ∈ g '' Set.Icc (0:ℝ) 1) : g (L g w) = w :=
  (L_mem hg hw).1

lemma g_R (hg : Continuous g) {w : X} (hw : w ∈ g '' Set.Icc (0:ℝ) 1) : g (R g w) = w :=
  (R_mem hg hw).1

lemma L_mem_Icc (hg : Continuous g) {w : X} (hw : w ∈ g '' Set.Icc (0:ℝ) 1) :
    L g w ∈ Set.Icc (0:ℝ) 1 := (L_mem hg hw).2

lemma R_mem_Icc (hg : Continuous g) {w : X} (hw : w ∈ g '' Set.Icc (0:ℝ) 1) :
    R g w ∈ Set.Icc (0:ℝ) 1 := (R_mem hg hw).2

lemma L_le {w : X} (hw : w ∈ g '' Set.Icc (0:ℝ) 1) {u : ℝ} (hu : u ∈ fibre g w) :
    L g w ≤ u :=
  csInf_le ⟨0, fun x hx => (Set.mem_Icc.mp hx.2).1⟩ hu

lemma le_R {w : X} (hw : w ∈ g '' Set.Icc (0:ℝ) 1) {u : ℝ} (hu : u ∈ fibre g w) :
    u ≤ R g w :=
  le_csSup ⟨1, fun x hx => (Set.mem_Icc.mp hx.2).2⟩ hu

lemma L_le_R (hg : Continuous g) {w : X} (hw : w ∈ g '' Set.Icc (0:ℝ) 1) : L g w ≤ R g w :=
  L_le hw (R_mem hg hw)

/-- Every fibre is an interval. -/
lemma fibre_interval (hfib : IsFibreInterval g) {w : X} {s t u : ℝ} (hs : s ∈ fibre g w)
    (hu : u ∈ fibre g w) (hst : s ≤ t) (htu : t ≤ u) : t ∈ fibre g w :=
  ⟨(hfib hs.2 hu.2 (hs.1.trans hu.1.symm) hst htu).trans hs.1,
    ⟨(Set.mem_Icc.mp hs.2).1.trans hst, htu.trans (Set.mem_Icc.mp hu.2).2⟩⟩

lemma mem_fibre_self {u : ℝ} (hu : u ∈ Set.Icc (0:ℝ) 1) : u ∈ fibre g (g u) := ⟨rfl, hu⟩

lemma mem_A_of {u : ℝ} (hu : u ∈ Set.Icc (0:ℝ) 1) : g u ∈ A g := ⟨u, hu, rfl⟩

lemma zero_mem_A : g 0 ∈ A g := ⟨0, ⟨le_rfl, zero_le_one⟩, rfl⟩

lemma one_mem_A : g 1 ∈ A g := ⟨1, ⟨zero_le_one, le_rfl⟩, rfl⟩

lemma Dset_subset_A : Dset g ⊆ A g := by
  rintro w ⟨t, ⟨ht, -⟩, rfl⟩
  exact ⟨t, ht, rfl⟩

lemma Dset_countable : (Dset g).Countable := by
  refine Set.Countable.image ?_ g
  refine Set.Countable.mono ?_ (Set.countable_range (fun q : ℚ => ((q : ℝ))) : (Set.range _).Countable)
  rintro t ⟨ht, q, rfl⟩
  exact ⟨q, rfl⟩

lemma zero_mem_Dset : g 0 ∈ Dset g := ⟨0, ⟨⟨le_rfl, zero_le_one⟩, ⟨0, by norm_num⟩⟩, rfl⟩

lemma one_mem_Dset : g 1 ∈ Dset g := ⟨1, ⟨⟨zero_le_one, le_rfl⟩, ⟨1, by norm_num⟩⟩, rfl⟩

lemma D0_countable : (D0 g).Countable :=
  Set.Countable.mono Set.sdiff_subset (Dset_countable (g := g))

lemma D0_subset_A : D0 g ⊆ A g := fun _ hw => Dset_subset_A hw.1

lemma L_zero (hg : Continuous g) : L g (g 0) = 0 :=
  le_antisymm (L_le zero_mem_A ⟨rfl, ⟨le_rfl, zero_le_one⟩⟩) (L_mem_Icc hg zero_mem_A).1

lemma L_zero_le (hg : Continuous g) {w : X} (hw : w ∈ A g) : L g (g 0) ≤ L g w := by
  rw [L_zero hg]; exact (L_mem_Icc hg hw).1

lemma LeMax (hg : Continuous g) (hfib : IsFibreInterval g) {w : X} (hw : w ∈ A g) :
    L g w ≤ L g (g 1) := by
  by_contra hcon
  push Not at hcon
  have h1 : (1:ℝ) ∈ fibre g (g 1) := ⟨rfl, ⟨zero_le_one, le_rfl⟩⟩
  have h2 : L g w ≤ 1 := (L_mem_Icc hg hw).2
  have hmem : L g w ∈ fibre g (g 1) :=
    fibre_interval hfib (L_mem hg one_mem_A) h1 (le_of_lt hcon) h2
  have h3 : g (L g w) = g 1 := hmem.1
  have h4 : g (L g w) = w := g_L hg hw
  have h5 : w = g 1 := h4.symm.trans h3
  have h6 : L g w = L g (g 1) := by rw [h5]
  linarith

lemma L_inj (hg : Continuous g) {w w' : X} (hw : w ∈ A g) (hw' : w' ∈ A g)
    (h : L g w = L g w') : w = w' := by
  rw [← g_L hg hw, ← g_L hg hw', h]

lemma R_lt_L (hg : Continuous g) (hfib : IsFibreInterval g) {a b : X} (ha : a ∈ A g)
    (hb : b ∈ A g) (hab : L g a < L g b) : R g a < L g b := by
  by_contra hcon
  push Not at hcon
  have hmem : L g b ∈ fibre g a :=
    fibre_interval hfib (L_mem hg ha) (R_mem hg ha) (le_of_lt hab) hcon
  have h1 : g (L g b) = a := hmem.1
  have h2 : g (L g b) = b := (L_mem hg hb).1
  have h3 : a = b := h1.symm.trans h2
  rw [h3] at hab
  exact (lt_irrefl _) hab

lemma L_zero_lt (hg : Continuous g) (hne : g 0 ≠ g 1) : L g (g 0) < L g (g 1) := by
  refine lt_of_le_of_ne (L_zero_le hg one_mem_A) ?_
  intro h
  exact hne (L_inj hg zero_mem_A one_mem_A h)

/-- Between two values with `L a < L b` there is a third. -/
lemma exists_between_A (hg : Continuous g) (hfib : IsFibreInterval g) {a b : X} (ha : a ∈ A g)
    (hb : b ∈ A g) (hab : L g a < L g b) : ∃ m ∈ A g, L g a < L g m ∧ L g m < L g b := by
  have hRL : R g a < L g b := R_lt_L hg hfib ha hb hab
  have h0 : (0:ℝ) ≤ R g a := (R_mem_Icc hg ha).1
  have h1 : L g b ≤ 1 := (L_mem_Icc hg hb).2
  obtain ⟨q, hq⟩ := exists_rat_btwn hRL
  have hqIcc : (q : ℝ) ∈ Set.Icc (0:ℝ) 1 :=
    ⟨le_of_lt (lt_of_le_of_lt h0 hq.1), le_of_lt (lt_of_lt_of_le hq.2 h1)⟩
  refine ⟨g q, mem_A_of hqIcc, ?_, ?_⟩
  · -- `L a < L (g q)`: otherwise `q` would lie in the fibre of `a`
    by_contra hcon
    push Not at hcon
    have hmem : (q : ℝ) ∈ fibre g (g q) := mem_fibre_self hqIcc
    have hqle : L g (g q) ≤ (q : ℝ) := L_le (mem_A_of hqIcc) hmem
    have hLa : L g a ≤ (q : ℝ) := le_of_lt (lt_of_le_of_lt (L_le_R hg ha) hq.1)
    have hmem2 : L g a ∈ fibre g (g q) :=
      fibre_interval hfib (L_mem hg (mem_A_of hqIcc)) hmem hcon hLa
    have h1' : a = g q := by rw [← hmem2.1, g_L hg ha]
    rw [← h1'] at hmem
    have h2 := le_R ha hmem
    linarith [hq.1]
  · -- `L (g q) < L b`
    have hmem : (q : ℝ) ∈ fibre g (g q) := mem_fibre_self hqIcc
    have hqle : L g (g q) ≤ (q : ℝ) := L_le (mem_A_of hqIcc) hmem
    linarith [hq.2]

lemma bddAbove_L (hg : Continuous g) {S : Set X} (hS : ∀ a ∈ S, a ∈ A g) :
    BddAbove (L g '' S) :=
  ⟨1, by rintro x ⟨a, ha, rfl⟩; exact (L_mem_Icc hg (hS a ha)).2⟩

lemma bddBelow_L (hg : Continuous g) {S : Set X} (hS : ∀ a ∈ S, a ∈ A g) :
    BddBelow (L g '' S) :=
  ⟨0, by rintro x ⟨a, ha, rfl⟩; exact (L_mem_Icc hg (hS a ha)).1⟩

lemma sSup_L_mem (hg : Continuous g) {S : Set X} (hS : ∀ a ∈ S, a ∈ A g) (hSne : S.Nonempty) :
    sSup (L g '' S) ∈ Set.Icc (0:ℝ) 1 := by
  have hcl : sSup (L g '' S) ∈ closure (L g '' S) :=
    csSup_mem_closure (hSne.image _) (bddAbove_L hg hS)
  refine closure_minimal (fun x hx => ?_) isClosed_Icc hcl
  obtain ⟨a, ha, rfl⟩ := hx
  exact L_mem_Icc hg (hS a ha)

lemma sInf_L_mem (hg : Continuous g) {S : Set X} (hS : ∀ a ∈ S, a ∈ A g) (hSne : S.Nonempty) :
    sInf (L g '' S) ∈ Set.Icc (0:ℝ) 1 := by
  have hcl : sInf (L g '' S) ∈ closure (L g '' S) :=
    csInf_mem_closure (hSne.image _) (bddBelow_L hg hS)
  refine closure_minimal (fun x hx => ?_) isClosed_Icc hcl
  obtain ⟨a, ha, rfl⟩ := hx
  exact L_mem_Icc hg (hS a ha)

/-- `g` of the supremum of the `L`-values of `S` is an upper bound of `S`. -/
lemma le_sSup_L (hg : Continuous g) (hfib : IsFibreInterval g) {S : Set X} (hS : ∀ a ∈ S, a ∈ A g)
    (hSne : S.Nonempty) {a : X} (ha : a ∈ S) :
    L g a ≤ L g (g (sSup (L g '' S))) := by
  by_contra hcon
  push Not at hcon
  have hσ : sSup (L g '' S) ∈ Set.Icc (0:ℝ) 1 := sSup_L_mem hg hS hSne
  have hmem : sSup (L g '' S) ∈ fibre g (g (sSup (L g '' S))) := mem_fibre_self hσ
  have ha' : L g a ≤ sSup (L g '' S) := le_csSup (bddAbove_L hg hS) ⟨a, ha, rfl⟩
  have hmem2 : L g a ∈ fibre g (g (sSup (L g '' S))) :=
    fibre_interval hfib (L_mem hg (mem_A_of hσ)) hmem (le_of_lt hcon) ha'
  have h1 : a = g (sSup (L g '' S)) := by rw [← hmem2.1, g_L hg (hS a ha)]
  rw [h1] at hcon
  exact (lt_irrefl _) hcon

/-- `g` of the supremum of the `L`-values of `S` is the least upper bound. -/
lemma sSup_L_le (hg : Continuous g) {S : Set X} (hS : ∀ a ∈ S, a ∈ A g) (hSne : S.Nonempty) {u : X}
    (hu : u ∈ A g) (hub : ∀ a ∈ S, L g a ≤ L g u) :
    L g (g (sSup (L g '' S))) ≤ L g u := by
  have hσ : sSup (L g '' S) ∈ Set.Icc (0:ℝ) 1 := sSup_L_mem hg hS hSne
  have hmem : sSup (L g '' S) ∈ fibre g (g (sSup (L g '' S))) := mem_fibre_self hσ
  have hle : L g (g (sSup (L g '' S))) ≤ sSup (L g '' S) := L_le (mem_A_of hσ) hmem
  have h2 : sSup (L g '' S) ≤ L g u :=
    csSup_le (hSne.image _) (by rintro x ⟨a, ha, rfl⟩; exact hub a ha)
  linarith

/-- `g` of the infimum of the `L`-values of `S` is a lower bound of `S`. -/
lemma sInf_L_le (hg : Continuous g) (hfib : IsFibreInterval g) {S : Set X} (hS : ∀ a ∈ S, a ∈ A g)
    (hSne : S.Nonempty) {a : X} (ha : a ∈ S) :
    L g (g (sInf (L g '' S))) ≤ L g a := by
  by_contra hcon
  push Not at hcon
  have hρ : sInf (L g '' S) ∈ Set.Icc (0:ℝ) 1 := sInf_L_mem hg hS hSne
  have hmem : sInf (L g '' S) ∈ fibre g (g (sInf (L g '' S))) := mem_fibre_self hρ
  have ha' : sInf (L g '' S) ≤ L g a := csInf_le (bddBelow_L hg hS) ⟨a, ha, rfl⟩
  have hle : L g (g (sInf (L g '' S))) ≤ sInf (L g '' S) := L_le (mem_A_of hρ) hmem
  linarith

/-- `g` of the infimum of the `L`-values of `S` is the greatest lower bound. -/
lemma le_sInf_L (hg : Continuous g) (hfib : IsFibreInterval g) {S : Set X} (hS : ∀ a ∈ S, a ∈ A g)
    (hSne : S.Nonempty) {u : X} (hu : u ∈ A g) (hub : ∀ a ∈ S, L g u ≤ L g a) :
    L g u ≤ L g (g (sInf (L g '' S))) := by
  by_contra hcon
  push Not at hcon
  have hρ : sInf (L g '' S) ∈ Set.Icc (0:ℝ) 1 := sInf_L_mem hg hS hSne
  have hmem : sInf (L g '' S) ∈ fibre g (g (sInf (L g '' S))) := mem_fibre_self hρ
  have h2 : L g u ≤ sInf (L g '' S) :=
    le_csInf (hSne.image _) (by rintro x ⟨a, ha, rfl⟩; exact hub a ha)
  have hmem2 : L g u ∈ fibre g (g (sInf (L g '' S))) :=
    fibre_interval hfib (L_mem hg (mem_A_of hρ)) hmem (le_of_lt hcon) h2
  have h1 : u = g (sInf (L g '' S)) := by rw [← hmem2.1, g_L hg hu]
  rw [h1] at hcon
  exact (lt_irrefl _) hcon

/-- A rational-time value strictly between two values. -/
lemma exists_Dset_btwn (hg : Continuous g) (hfib : IsFibreInterval g) {a b : X} (ha : a ∈ A g)
    (hb : b ∈ A g) (hab : L g a < L g b) : ∃ d ∈ Dset g, L g a < L g d ∧ L g d < L g b := by
  have hRL : R g a < L g b := R_lt_L hg hfib ha hb hab
  have h0 : (0:ℝ) ≤ R g a := (R_mem_Icc hg ha).1
  have h1 : L g b ≤ 1 := (L_mem_Icc hg hb).2
  obtain ⟨q, hq1, hq2⟩ := exists_rat_btwn hRL
  have hqIcc : (q : ℝ) ∈ Set.Icc (0:ℝ) 1 :=
    ⟨le_of_lt (lt_of_le_of_lt h0 hq1), le_of_lt (lt_of_lt_of_le hq2 h1)⟩
  refine ⟨g q, ⟨q, ⟨hqIcc, ⟨q, rfl⟩⟩, rfl⟩, ?_, ?_⟩
  · by_contra hcon
    push Not at hcon
    have hmem : (q : ℝ) ∈ fibre g (g q) := mem_fibre_self hqIcc
    have hqle : L g (g q) ≤ (q : ℝ) := L_le (mem_A_of hqIcc) hmem
    have hLa : L g a ≤ (q : ℝ) := le_of_lt (lt_of_le_of_lt (L_le_R hg ha) hq1)
    have hmem2 : L g a ∈ fibre g (g q) :=
      fibre_interval hfib (L_mem hg (mem_A_of hqIcc)) hmem hcon hLa
    have h1' : a = g q := by rw [← hmem2.1, g_L hg ha]
    rw [← h1'] at hmem
    have h2 := le_R ha hmem
    linarith
  · have hmem : (q : ℝ) ∈ fibre g (g q) := mem_fibre_self hqIcc
    have hqle : L g (g q) ≤ (q : ℝ) := L_le (mem_A_of hqIcc) hmem
    linarith

/-- A rational value other than the endpoints, strictly between two values. -/
lemma exists_D0_btwn (hg : Continuous g) (hfib : IsFibreInterval g) (hne : g 0 ≠ g 1) {a b : X}
    (ha : a ∈ A g) (hb : b ∈ A g) (hab : L g a < L g b) :
    ∃ d ∈ D0 g, L g a < L g d ∧ L g d < L g b := by
  obtain ⟨d, hdD, hda, hdb⟩ := exists_Dset_btwn hg hfib ha hb hab
  have hdA : d ∈ A g := Dset_subset_A hdD
  have hd0 : d ≠ g 0 := by
    intro h
    have : L g d = L g (g 0) := by rw [h]
    rw [L_zero hg] at this
    linarith [L_zero_le hg ha, L_zero hg]
  have hd1 : d ≠ g 1 := by
    intro h
    have : L g d = L g (g 1) := by rw [h]
    have hle := LeMax hg hfib hb
    linarith
  exact ⟨d, ⟨hdD, by simp [hd0, hd1]⟩, hda, hdb⟩

lemma W_countable : (W g).Countable := (D0_countable (g := g)).image (L g)

lemma W_dense (hg : Continuous g) (hfib : IsFibreInterval g) (hne : g 0 ≠ g 1) {x y : ℝ}
    (hx : x ∈ W g) (hy : y ∈ W g) (hxy : x < y) : ∃ z ∈ W g, x < z ∧ z < y := by
  obtain ⟨a, haD, rfl⟩ := hx
  obtain ⟨b, hbD, rfl⟩ := hy
  obtain ⟨d, hdD, h1, h2⟩ := exists_D0_btwn hg hfib hne (D0_subset_A haD) (D0_subset_A hbD) hxy
  exact ⟨L g d, ⟨d, hdD, rfl⟩, h1, h2⟩

lemma W_noMin (hg : Continuous g) (hfib : IsFibreInterval g) (hne : g 0 ≠ g 1) {x : ℝ}
    (hx : x ∈ W g) : ∃ y ∈ W g, y < x := by
  obtain ⟨a, haD, rfl⟩ := hx
  have ha : a ∈ A g := D0_subset_A haD
  have hne0 : a ≠ g 0 := fun h => haD.2 (by simp [h])
  have hlt : L g (g 0) < L g a := by
    refine lt_of_le_of_ne (L_zero_le hg ha) ?_
    intro h
    exact hne0 (L_inj hg (w := g 0) (w' := a) zero_mem_A ha h).symm
  obtain ⟨d, hdD, h1, h2⟩ := exists_D0_btwn hg hfib hne zero_mem_A ha hlt
  exact ⟨L g d, ⟨d, hdD, rfl⟩, h2⟩

lemma W_noMax (hg : Continuous g) (hfib : IsFibreInterval g) (hne : g 0 ≠ g 1) {x : ℝ}
    (hx : x ∈ W g) : ∃ y ∈ W g, x < y := by
  obtain ⟨a, haD, rfl⟩ := hx
  have ha : a ∈ A g := D0_subset_A haD
  have hne1 : a ≠ g 1 := fun h => haD.2 (by simp [h])
  have hlt : L g a < L g (g 1) := by
    refine lt_of_le_of_ne (LeMax hg hfib ha) ?_
    intro h
    exact hne1 (L_inj hg (w := a) (w' := g 1) ha one_mem_A h)
  obtain ⟨d, hdD, h1, h2⟩ := exists_D0_btwn hg hfib hne ha one_mem_A hlt
  exact ⟨L g d, ⟨d, hdD, rfl⟩, h1⟩

lemma W_nonempty (hg : Continuous g) (hfib : IsFibreInterval g) (hne : g 0 ≠ g 1) :
    (W g).Nonempty := by
  obtain ⟨d, hdD, -⟩ := exists_D0_btwn hg hfib hne zero_mem_A one_mem_A (L_zero_lt hg hne)
  exact ⟨L g d, ⟨d, hdD, rfl⟩⟩


/-- **Left interval neighbourhood.**  Every neighbourhood `O` of `z ∈ A` contains all values whose
`L`-value lies in an interval `(L a, L z]` just below `L z`; `a` is the value of `g` at times up to
`L z - δ/2`, where `δ` is a continuity modulus of `g` at `L z`. -/
lemma left_Icc (hg : Continuous g) (hfib : IsFibreInterval g) {z : X} (hz : z ∈ A g)
    {O : Set X} (hO : IsOpen O) (hzO : z ∈ O) :
    ∃ a ∈ A g, L g a ≤ L g z ∧ ∀ w ∈ A g, L g a < L g w → L g w ≤ L g z → w ∈ O := by
  have hLO : g (L g z) ∈ O := by rw [g_L hg hz]; exact hzO
  obtain ⟨δ, hδpos, hδ⟩ :=
    Metric.mem_nhds_iff.mp (hg.continuousAt.preimage_mem_nhds (hO.mem_nhds hLO))
  have hδ2 : 0 < δ / 2 := by linarith
  have hz0 : 0 ≤ L g z := (L_mem_Icc hg hz).1
  have hz1 : L g z ≤ 1 := (L_mem_Icc hg hz).2
  set T : Set ℝ := Set.Icc (0:ℝ) (max 0 (L g z - δ / 2)) with hT
  have hTsub : T ⊆ Set.Icc (0:ℝ) 1 :=
    fun u hu => ⟨hu.1, le_trans hu.2 (max_le zero_le_one (by linarith))⟩
  have hS : ∀ a ∈ g '' T, a ∈ A g := by
    rintro a ⟨u, hu, rfl⟩
    exact mem_A_of (hTsub hu)
  have hSne : (g '' T).Nonempty := ⟨g 0, 0, ⟨le_refl 0, le_max_left 0 _⟩, rfl⟩
  refine ⟨g (sSup (L g '' (g '' T))), mem_A_of (sSup_L_mem hg hS hSne), ?_, ?_⟩
  · refine sSup_L_le hg hS hSne hz (fun a ha => ?_)
    obtain ⟨u, hu, rfl⟩ := ha
    have h1 : L g (g u) ≤ u := L_le (mem_A_of (hTsub hu)) (mem_fibre_self (hTsub hu))
    have h2 : u ≤ L g z := le_trans hu.2 (max_le hz0 (by linarith))
    linarith
  · intro w hw haw hwz
    by_cases heq : L g w = L g z
    · rw [L_inj hg hw hz heq]; exact hzO
    · have hlt : L g w < L g z := lt_of_le_of_ne hwz heq
      have hlow : L g z - δ / 2 < L g w := by
        by_contra hcon
        push Not at hcon
        have hmemT : L g w ∈ T := by
          refine ⟨(L_mem_Icc hg hw).1, ?_⟩
          by_cases h : L g z - δ / 2 ≤ 0
          · rw [max_eq_left h]; linarith
          · rw [max_eq_right (not_le.mp h).le]; exact hcon
        have h5 : L g w ≤ L g (g (sSup (L g '' (g '' T)))) :=
          le_sSup_L (a := w) hg hfib hS hSne ⟨L g w, hmemT, g_L hg hw⟩
        linarith
      have h1 : g (L g w) ∈ O := hδ (by
        rw [Metric.mem_ball, Real.dist_eq]
        exact abs_lt.mpr ⟨by linarith, by linarith⟩)
      rwa [g_L hg hw] at h1

set_option maxHeartbeats 1000000 in
lemma left_Icc_min (hg : Continuous g) (hfib : IsFibreInterval g) {z : X} (hz : z ∈ A g)
    {O : Set X} (hO : IsOpen O) (hzO : z ∈ O) :
    ∃ a ∈ A g, L g a ≤ L g z ∧ (L g a = L g z → z = g 0) ∧
      ∀ w ∈ A g, L g a < L g w → L g w ≤ L g z → w ∈ O := by
  have hLO : g (L g z) ∈ O := by rw [g_L hg hz]; exact hzO
  obtain ⟨δ, hδpos, hδ⟩ :=
    Metric.mem_nhds_iff.mp (hg.continuousAt.preimage_mem_nhds (hO.mem_nhds hLO))
  have hδ2 : 0 < δ / 2 := by linarith
  have hz0 : 0 ≤ L g z := (L_mem_Icc hg hz).1
  have hz1 : L g z ≤ 1 := (L_mem_Icc hg hz).2
  set T : Set ℝ := Set.Icc (0:ℝ) (max 0 (L g z - δ / 2)) with hT
  have hTsub : T ⊆ Set.Icc (0:ℝ) 1 :=
    fun u hu => ⟨hu.1, le_trans hu.2 (max_le zero_le_one (by linarith))⟩
  have hS : ∀ a ∈ g '' T, a ∈ A g := by
    rintro a ⟨u, hu, rfl⟩
    exact mem_A_of (hTsub hu)
  have hSne : (g '' T).Nonempty := ⟨g 0, 0, ⟨le_refl 0, le_max_left 0 _⟩, rfl⟩
  refine ⟨g (sSup (L g '' (g '' T))), mem_A_of (sSup_L_mem hg hS hSne), ?_, ?_, ?_⟩
  · refine sSup_L_le hg hS hSne hz (fun a ha => ?_)
    obtain ⟨u, hu, rfl⟩ := ha
    have h1 : L g (g u) ≤ u := L_le (mem_A_of (hTsub hu)) (mem_fibre_self (hTsub hu))
    have h2 : u ≤ L g z := le_trans hu.2 (max_le hz0 (by linarith))
    linarith
  · intro hEq
    have hσ : sSup (L g '' (g '' T)) ∈ Set.Icc (0:ℝ) 1 := sSup_L_mem hg hS hSne
    have h1 : L g z ≤ sSup (L g '' (g '' T)) := by
      rw [← hEq]
      exact L_le (mem_A_of hσ) (mem_fibre_self hσ)
    have h2 : sSup (L g '' (g '' T)) ≤ max 0 (L g z - δ / 2) := by
      refine csSup_le (hSne.image _) ?_
      rintro x ⟨w, ⟨u, hu, rfl⟩, rfl⟩
      exact le_trans (L_le (mem_A_of (hTsub hu)) (mem_fibre_self (hTsub hu))) hu.2
    have h3 : max 0 (L g z - δ / 2) ≤ L g z := max_le hz0 (by linarith)
    have h4 : L g z = max 0 (L g z - δ / 2) := le_antisymm (le_trans h1 h2) h3
    have h5 : L g z = 0 := by
      rcases le_total (0:ℝ) (L g z - δ / 2) with h | h
      · rw [max_eq_right h] at h4; linarith
      · rw [max_eq_left h] at h4; exact h4
    have h6 : L g z = L g (g 0) := h5.trans (L_zero hg).symm
    exact L_inj hg hz zero_mem_A h6
  · intro w hw haw hwz
    by_cases heq : L g w = L g z
    · rw [L_inj hg hw hz heq]; exact hzO
    · have hlt : L g w < L g z := lt_of_le_of_ne hwz heq
      have hlow : L g z - δ / 2 < L g w := by
        by_contra hcon
        push Not at hcon
        have hmemT : L g w ∈ T := by
          refine ⟨(L_mem_Icc hg hw).1, ?_⟩
          by_cases h : L g z - δ / 2 ≤ 0
          · rw [max_eq_left h]; linarith
          · rw [max_eq_right (not_le.mp h).le]; exact hcon
        have h5 : L g w ≤ L g (g (sSup (L g '' (g '' T)))) :=
          le_sSup_L (a := w) hg hfib hS hSne ⟨L g w, hmemT, g_L hg hw⟩
        linarith
      have h1 : g (L g w) ∈ O := hδ (by
        rw [Metric.mem_ball, Real.dist_eq]
        exact abs_lt.mpr ⟨by linarith, by linarith⟩)
      rwa [g_L hg hw] at h1

/-- **Right interval neighbourhood.**  For `z ≠ g 1`, every neighbourhood `O` of `z` contains all
values whose `L`-value lies in an interval `[L z, L b)` just above `L z`; here
`b = g (min 1 (R z + δ/2))` with `δ` a continuity modulus of `g` at `R z`. -/
lemma right_Icc (hg : Continuous g) (hfib : IsFibreInterval g) {z : X} (hz : z ∈ A g)
    (hz1 : z ≠ g 1) {O : Set X} (hO : IsOpen O) (hzO : z ∈ O) :
    ∃ b ∈ A g, L g z < L g b ∧ ∀ w ∈ A g, L g z ≤ L g w → L g w < L g b → w ∈ O := by
  have hRO : g (R g z) ∈ O := by rw [g_R hg hz]; exact hzO
  obtain ⟨δ, hδpos, hδ⟩ :=
    Metric.mem_nhds_iff.mp (hg.continuousAt.preimage_mem_nhds (hO.mem_nhds hRO))
  have hδ2 : 0 < δ / 2 := by linarith
  have hρ0 : 0 ≤ R g z := (R_mem_Icc hg hz).1
  have hρ1 : R g z ≤ 1 := (R_mem_Icc hg hz).2
  have hlr : L g z ≤ R g z := L_le_R hg hz
  have huIcc : min 1 (R g z + δ / 2) ∈ Set.Icc (0:ℝ) 1 :=
    ⟨le_trans hρ0 (le_min hρ1 (by linarith)), min_le_left _ _⟩
  have hρu : R g z ≤ min 1 (R g z + δ / 2) := le_min hρ1 (by linarith)
  have hufib : min 1 (R g z + δ / 2) ∈ fibre g (g (min 1 (R g z + δ / 2))) :=
    mem_fibre_self huIcc
  have hAu : g (min 1 (R g z + δ / 2)) ∈ A g := mem_A_of huIcc
  refine ⟨g (min 1 (R g z + δ / 2)), hAu, ?_, ?_⟩
  · by_contra hcon
    push Not at hcon
    have hmb : g (L g z) = g (min 1 (R g z + δ / 2)) := by
      have h1 : g (L g (g (min 1 (R g z + δ / 2)))) = g (min 1 (R g z + δ / 2)) :=
        (L_mem hg hAu).1
      have h2 : g (L g z) = g (L g (g (min 1 (R g z + δ / 2)))) :=
        hfib (s := L g (g (min 1 (R g z + δ / 2)))) (t := L g z)
          (u := min 1 (R g z + δ / 2)) (L_mem hg hAu).2 huIcc (h1.trans rfl)
          hcon (le_trans hlr hρu)
      rw [h2, h1]
    have hmem : L g z ∈ fibre g (g (min 1 (R g z + δ / 2))) := ⟨hmb, L_mem_Icc hg hz⟩
    have h1 : z = g (min 1 (R g z + δ / 2)) := by rw [← hmem.1, g_L hg hz]
    have h2 : min 1 (R g z + δ / 2) ∈ fibre g z := ⟨h1.symm, huIcc⟩
    have h3 : min 1 (R g z + δ / 2) = R g z := le_antisymm (le_R hz h2) hρu
    have h4 : R g z = 1 := by
      rcases le_total (R g z + δ / 2) 1 with h | h
      · rw [min_eq_right h] at h3; linarith
      · rw [min_eq_left h] at h3; linarith
    have h5 : (1:ℝ) ∈ fibre g z := by rw [← h4]; exact R_mem hg hz
    exact hz1 h5.1.symm
  · intro w hw hlw hwb
    by_cases heq : L g w = L g z
    · rw [L_inj hg hw hz heq]; exact hzO
    · have hgt : L g z < L g w := lt_of_le_of_ne hlw (fun h => heq h.symm)
      have hρlw : R g z ≤ L g w := by
        by_contra hcon
        push Not at hcon
        have hmem : L g w ∈ fibre g z :=
          fibre_interval (w := z) (s := L g z) (u := R g z) (t := L g w)
            hfib (L_mem hg hz) (R_mem hg hz) hlw (le_of_lt hcon)
        have h1 : w = g (L g w) := (g_L hg hw).symm
        rw [hmem.1] at h1
        have h2 : L g w = L g z := by rw [h1]
        linarith
      have hle : L g w < R g z + δ / 2 := by
        have h6 : L g (g (min 1 (R g z + δ / 2))) ≤ min 1 (R g z + δ / 2) := L_le hAu hufib
        have h7 : min 1 (R g z + δ / 2) ≤ R g z + δ / 2 := min_le_right _ _
        linarith
      have h1 : g (L g w) ∈ O := hδ (by
        rw [Metric.mem_ball, Real.dist_eq]
        exact abs_lt.mpr ⟨by linarith, by linarith⟩)
      rwa [g_L hg hw] at h1

end Basic
/-- **Arc extraction.**  A continuous map with interval fibres separating its endpoints has a
continuous reparametrisation that is injective on `[0,1]`. -/
theorem exists_arc_of_interval_fibres {X : Type*} [MetricSpace X] {g : ℝ → X} (hg : Continuous g)
    (hfib : IsFibreInterval g) (hne : g 0 ≠ g 1) :
    ∃ γ : ℝ → X, Continuous γ ∧ Set.InjOn γ (Set.Icc (0:ℝ) 1) ∧ γ 0 = g 0 ∧ γ 1 = g 1 := by
  classical
  haveI : Nonempty ↥(W g) := by
    obtain ⟨x, hx⟩ := W_nonempty hg hfib hne
    exact ⟨⟨x, hx⟩⟩
  haveI : Countable ↥(W g) := (W_countable (g := g)).to_subtype
  haveI : DenselyOrdered ↥(W g) := ⟨fun x y hxy => by
    obtain ⟨z, hz, h1, h2⟩ := W_dense hg hfib hne x.2 y.2 hxy
    exact ⟨⟨z, hz⟩, h1, h2⟩⟩
  haveI : NoMinOrder ↥(W g) := ⟨fun x => by
    obtain ⟨y, hy, h1⟩ := W_noMin hg hfib hne x.2
    exact ⟨⟨y, hy⟩, h1⟩⟩
  haveI : NoMaxOrder ↥(W g) := ⟨fun x => by
    obtain ⟨y, hy, h1⟩ := W_noMax hg hfib hne x.2
    exact ⟨⟨y, hy⟩, h1⟩⟩
  haveI : Nonempty ↥(Set.Ioo (0:ℚ) 1) := ⟨⟨1/2, by norm_num⟩⟩
  obtain ⟨φ⟩ := Order.iso_of_countable_dense ↥(W g) ↥(Set.Ioo (0:ℚ) 1)
  let Psi : ℝ → ℝ := fun x => if h : x ∈ W g then ((φ ⟨x, h⟩ : ℚ) : ℝ) else 0
  have Psi_of_mem : ∀ {x : ℝ} (hx : x ∈ W g), Psi x = ((φ ⟨x, hx⟩ : ℚ) : ℝ) :=
    fun hx => dif_pos hx
  have Psi_mem : ∀ {x : ℝ} (hx : x ∈ W g), Psi x ∈ Set.Ioo (0:ℝ) 1 := by
    intro x hx
    rw [Psi_of_mem hx]
    have h : ((φ ⟨x, hx⟩ : ↥(Set.Ioo (0:ℚ) 1)) : ℚ) ∈ Set.Ioo (0:ℚ) 1 := (φ ⟨x, hx⟩).2
    exact ⟨by exact_mod_cast h.1, by exact_mod_cast h.2⟩
  have Psi_le : ∀ {x y : ℝ} (hx : x ∈ W g) (hy : y ∈ W g), Psi x ≤ Psi y ↔ x ≤ y := by
    intro x y hx hy
    rw [Psi_of_mem hx, Psi_of_mem hy, Rat.cast_le]
    exact φ.le_iff_le
  have Psi_surj : ∀ q : ℚ, q ∈ Set.Ioo (0:ℚ) 1 → ∃ x ∈ W g, Psi x = (q : ℝ) := by
    intro q hq
    refine ⟨(φ.symm ⟨q, hq⟩).1, (φ.symm ⟨q, hq⟩).2, ?_⟩
    rw [Psi_of_mem (φ.symm ⟨q, hq⟩).2]
    have h1 : ((φ (φ.symm ⟨q, hq⟩) : ↥(Set.Ioo (0:ℚ) 1)) : ℚ) = q := by
      rw [OrderIso.apply_symm_apply]
    exact_mod_cast h1
  have Psi_dense : ∀ {x : ℝ} (hx : x ∈ W g) (t : ℝ), t < Psi x →
      ∃ y ∈ W g, t < Psi y ∧ Psi y < Psi x := by
    intro x hx t ht
    have hxmem := Psi_mem hx
    have hlt : max t 0 < min (Psi x) 1 :=
      max_lt (lt_min ht (lt_trans ht hxmem.2)) (lt_min hxmem.1 one_pos)
    obtain ⟨q, hq1, hq2⟩ := exists_rat_btwn hlt
    have hq : q ∈ Set.Ioo (0:ℚ) 1 := by
      refine ⟨?_, ?_⟩
      · exact_mod_cast (lt_of_le_of_lt (le_max_right t 0) hq1)
      · exact_mod_cast (lt_of_lt_of_le hq2 (min_le_right (Psi x) 1))
    obtain ⟨y, hy, hyq⟩ := Psi_surj q hq
    exact ⟨y, hy, by rw [hyq]; exact lt_of_le_of_lt (le_max_left t 0) hq1,
      by rw [hyq]; exact lt_of_lt_of_le hq2 (min_le_left (Psi x) 1)⟩
  -- the parametrisation
  let Sfun : ℝ → Set X := fun t => {d | d ∈ D0 g ∧ Psi (L g d) ≤ t}
  let gam : ℝ → X := fun t => g (sSup (L g '' Sfun t))
  have Ssub : ∀ t, ∀ a ∈ Sfun t, a ∈ A g := fun t a ha => D0_subset_A ha.1

  have gam_mem : ∀ t, gam t ∈ A g := by
    intro t
    by_cases hne' : (Sfun t).Nonempty
    · exact mem_A_of (sSup_L_mem hg (Ssub t) hne')
    · have h_empty : L g '' Sfun t = ∅ :=
        Set.image_eq_empty.mpr (Set.not_nonempty_iff_eq_empty.mp hne')
      change g (sSup (L g '' Sfun t)) ∈ A g
      rw [h_empty, Real.sSup_empty]
      exact zero_mem_A
  have char_fwd : ∀ {t : ℝ} {d : X}, d ∈ D0 g → Psi (L g d) ≤ t → L g d ≤ L g (gam t) := by
    intro t d hd h
    exact le_sSup_L hg hfib (Ssub t) ⟨d, hd, h⟩ ⟨hd, h⟩
  have char_bwd : ∀ {t : ℝ} {d : X}, d ∈ D0 g → L g d ≤ L g (gam t) → Psi (L g d) ≤ t := by
    intro t d hd h
    by_contra hcon
    push Not at hcon
    have hLdW : L g d ∈ W g := ⟨d, hd, rfl⟩
    obtain ⟨y, hyW, hty, hylt⟩ := Psi_dense hLdW t hcon
    obtain ⟨d', hd'D, hd'eq⟩ := hyW
    have hLd'W : L g d' ∈ W g := ⟨d', hd'D, rfl⟩
    have hub : ∀ a ∈ Sfun t, L g a ≤ L g d' := by
      intro a ha
      have hLaW : L g a ∈ W g := ⟨a, ha.1, rfl⟩
      have hlt : Psi (L g a) < Psi (L g d') := by
        rw [hd'eq]; exact lt_of_le_of_lt ha.2 hty
      by_contra hcon'
      push Not at hcon'
      have := (Psi_le hLd'W hLaW).mpr (le_of_lt hcon')
      linarith
    have hle : L g (gam t) ≤ L g d' := by
      by_cases hne' : (Sfun t).Nonempty
      · exact sSup_L_le hg (Ssub t) hne' (D0_subset_A hd'D) hub
      · have h_empty : L g '' Sfun t = ∅ :=
          Set.image_eq_empty.mpr (Set.not_nonempty_iff_eq_empty.mp hne')
        change L g (g (sSup (L g '' Sfun t))) ≤ L g d'
        rw [h_empty, Real.sSup_empty, L_zero hg]
        exact (L_mem_Icc hg (D0_subset_A hd'D)).1
    have h1 : L g d' < L g d := by
      by_contra hcon2
      push Not at hcon2
      have h7 : Psi (L g d) ≤ Psi (L g d') := (Psi_le hLdW hLd'W).mpr hcon2
      have h8 : Psi (L g d') < Psi (L g d) := by rw [hd'eq]; exact hylt
      linarith
    linarith
  have char_iff : ∀ {t : ℝ} {d : X}, d ∈ D0 g → (Psi (L g d) ≤ t ↔ L g d ≤ L g (gam t)) :=
    fun hd => ⟨fun h => char_fwd hd h, fun h => char_bwd hd h⟩
  have gam_mono : ∀ {t t' : ℝ}, t ≤ t' → L g (gam t) ≤ L g (gam t') := by
    intro t t' htt'
    by_cases hne' : (Sfun t).Nonempty
    · refine sSup_L_le hg (Ssub t) hne' (gam_mem t') (fun a ha => ?_)
      exact le_sSup_L hg hfib (Ssub t') ⟨a, ha.1, le_trans ha.2 htt'⟩ ⟨ha.1, le_trans ha.2 htt'⟩
    · have h_empty : L g '' Sfun t = ∅ :=
        Set.image_eq_empty.mpr (Set.not_nonempty_iff_eq_empty.mp hne')
      change L g (g (sSup (L g '' Sfun t))) ≤ L g (gam t')
      rw [h_empty, Real.sSup_empty, L_zero hg]
      exact (L_mem_Icc hg (gam_mem t')).1
  have gam_lt : ∀ {t t' : ℝ}, t < t' → t < 1 → 0 < t' → L g (gam t) < L g (gam t') := by
    intro t t' htt' ht1 ht'0
    have hlt : max t 0 < min t' 1 := max_lt (lt_min htt' ht1) (lt_min ht'0 one_pos)
    obtain ⟨q, hq1, hq2⟩ := exists_rat_btwn hlt
    have hq : q ∈ Set.Ioo (0:ℚ) 1 := by
      refine ⟨?_, ?_⟩
      · exact_mod_cast (lt_of_le_of_lt (le_max_right t 0) hq1)
      · exact_mod_cast (lt_of_lt_of_le hq2 (min_le_right t' 1))
    obtain ⟨x, hxW, hxq⟩ := Psi_surj q hq
    obtain ⟨d, hdD, hdLe⟩ := hxW
    have h1 : ¬ (Psi (L g d) ≤ t) := by
      rw [hdLe, hxq]
      exact not_le.mpr (lt_of_le_of_lt (le_max_left t 0) hq1)
    have h2 : Psi (L g d) ≤ t' := by
      rw [hdLe, hxq]
      exact le_of_lt (lt_of_lt_of_le hq2 (min_le_left t' 1))
    have h3 : L g (gam t) < L g d := by
      by_contra hcon
      push Not at hcon
      exact h1 ((char_iff hdD).mpr hcon)
    have h4 : L g d ≤ L g (gam t') := (char_iff hdD).mp h2
    linarith
  have gam_zero : gam 0 = g 0 := by
    have hempty : Sfun 0 = ∅ := by
      ext d
      constructor
      · rintro ⟨hd, h⟩
        exact absurd h (not_le.mpr (Psi_mem ⟨d, hd, rfl⟩).1)
      · intro h; exact absurd h (Set.notMem_empty d)
    change g (sSup (L g '' Sfun 0)) = g 0
    rw [hempty, Set.image_empty, Real.sSup_empty]
  have gam_one : gam 1 = g 1 := by
    have hne1 : (Sfun 1).Nonempty := by
      obtain ⟨d, hdD, -⟩ := exists_D0_btwn hg hfib hne zero_mem_A one_mem_A (L_zero_lt hg hne)
      exact ⟨d, hdD, le_of_lt (Psi_mem ⟨d, hdD, rfl⟩).2⟩
    have h1 : L g (gam 1) ≤ L g (g 1) :=
      sSup_L_le hg (Ssub 1) hne1 one_mem_A (fun a ha => LeMax hg hfib (D0_subset_A ha.1))
    have h2 : L g (g 1) ≤ L g (gam 1) := by
      by_contra hcon
      push Not at hcon
      obtain ⟨d, hdD, hd1, hd2⟩ := exists_D0_btwn hg hfib hne (gam_mem 1) one_mem_A hcon
      have hdmem : d ∈ Sfun 1 := ⟨hdD, le_of_lt (Psi_mem ⟨d, hdD, rfl⟩).2⟩
      have h3 : L g d ≤ sSup (L g '' Sfun 1) :=
        le_csSup (bddAbove_L hg (Ssub 1)) ⟨d, hdmem, rfl⟩
      have hσ : sSup (L g '' Sfun 1) ∈ Set.Icc (0:ℝ) 1 := sSup_L_mem hg (Ssub 1) hne1
      have h4 : L g d ∈ fibre g (g (sSup (L g '' Sfun 1))) :=
        fibre_interval hfib (L_mem hg (mem_A_of hσ)) (mem_fibre_self hσ)
          (le_of_lt hd1) h3
      have h5 : d = gam 1 := by
        change d = g (sSup (L g '' Sfun 1))
        rw [← h4.1, g_L hg (D0_subset_A hdD)]
      have h6 : L g d = L g (gam 1) := by rw [h5]
      linarith
    exact L_inj hg (gam_mem 1) one_mem_A (le_antisymm h1 h2)
  -- monotonicity in `X`-terms for elements of `[0,1]`
  have gam_mono_A : ∀ {t t' : ℝ}, 0 ≤ t → t ≤ t' → t' ≤ 1 → L g (gam t) ≤ L g (gam t') :=
    fun _ htt' _ => gam_mono htt'
  have exists_lt_gam : ∀ {t : ℝ} {a : X}, a ∈ A g → L g a < L g (gam t) →
      ∃ t' < t, L g a < L g (gam t') := by
    intro t a ha hat
    obtain ⟨d, hdD, hda, hdg⟩ := exists_D0_btwn hg hfib hne ha (gam_mem t) hat
    have h1 : Psi (L g d) ≤ t := (char_iff hdD).mpr (le_of_lt hdg)
    have h2 : Psi (L g d) < t := by
      rcases lt_or_eq_of_le h1 with h | h
      · exact h
      · obtain ⟨d'', hd''D, hd''1, hd''2⟩ :=
          exists_D0_btwn hg hfib hne (D0_subset_A hdD) (gam_mem t) hdg
        have h3 : Psi (L g d'') ≤ t := (char_iff hd''D).mpr (le_of_lt hd''2)
        have h4le : Psi (L g d) ≤ Psi (L g d'') :=
          (Psi_le ⟨d, hdD, rfl⟩ ⟨d'', hd''D, rfl⟩).mpr (le_of_lt hd''1)
        have h4ne : Psi (L g d) ≠ Psi (L g d'') := by
          intro heq
          have h5 := (Psi_le ⟨d, hdD, rfl⟩ ⟨d'', hd''D, rfl⟩).mp (le_of_eq heq)
          have h6 := (Psi_le ⟨d'', hd''D, rfl⟩ ⟨d, hdD, rfl⟩).mp (le_of_eq heq.symm)
          linarith
        have h4 : Psi (L g d) < Psi (L g d'') := lt_of_le_of_ne h4le h4ne
        linarith
    exact ⟨Psi (L g d), h2, lt_of_lt_of_le hda (char_fwd hdD le_rfl)⟩
  have exists_gt_gam : ∀ {t : ℝ} {b : X}, b ∈ A g → L g (gam t) < L g b →
      ∃ t' > t, L g (gam t') < L g b := by
    intro t b hb hbt
    obtain ⟨d, hdD, hdt, hdb⟩ := exists_D0_btwn hg hfib hne (gam_mem t) hb hbt
    have hgt : t < Psi (L g d) := by
      by_contra hcon
      push Not at hcon
      exact absurd ((char_iff hdD).mp hcon) (not_le.mpr hdt)
    refine ⟨Psi (L g d), hgt, ?_⟩
    refine lt_of_le_of_lt ?_ hdb
    refine sSup_L_le hg (Ssub (Psi (L g d))) ⟨d, hdD, le_rfl⟩ (D0_subset_A hdD) ?_
    intro c hc
    exact (Psi_le ⟨c, hc.1, rfl⟩ ⟨d, hdD, rfl⟩).mp hc.2

  -- the arc: `gam` reparametrised by the projection onto `[0,1]`, extended by constants
  let γ : ℝ → X := fun t => gam ((Set.projIcc (0:ℝ) 1 zero_le_one t : ↥(Set.Icc (0:ℝ) 1)) : ℝ)
  have hγmem : ∀ {t : ℝ}, t ∈ Set.Icc (0:ℝ) 1 → γ t = gam t := by
    intro t ht
    have h1 : (Set.projIcc (0:ℝ) 1 zero_le_one t : ↥(Set.Icc (0:ℝ) 1)) = ⟨t, ht⟩ :=
      Set.projIcc_of_mem zero_le_one ht
    simp only [γ]
    rw [h1]
  have hγinj : Set.InjOn γ (Set.Icc (0:ℝ) 1) := by
    intro t ht t' ht' heq
    rw [hγmem ht, hγmem ht'] at heq
    by_contra hne'
    rcases lt_or_gt_of_ne hne' with h | h
    · have h2 := gam_lt (t := t) (t' := t') h (lt_of_lt_of_le h ht'.2) (lt_of_le_of_lt ht.1 h)
      rw [heq] at h2
      exact (lt_irrefl _) h2
    · have h2 := gam_lt (t := t') (t' := t) h (lt_of_lt_of_le h ht.2) (lt_of_le_of_lt ht'.1 h)
      rw [heq] at h2
      exact (lt_irrefl _) h2
  have hγ0 : γ 0 = g 0 := by
    rw [hγmem ⟨le_rfl, zero_le_one⟩, gam_zero]
  have hγ1 : γ 1 = g 1 := by
    rw [hγmem ⟨zero_le_one, le_rfl⟩, gam_one]
  -- continuity of `gam` on `[0,1]`: the left/right interval neighbourhoods.
  -- Plan (verified): `left_Icc`/`right_Icc` give `a ≤ z ≺ b` with `O`-conditions; `exists_lt_gam`/
  -- `exists_gt_gam` give the window `t₁ < t < t₂`; the modulus is `min (t - t₁) (t₂ - t)`, with the
  -- exceptional case `L a = L z` (which forces `z = g 0`, hence `t = 0`) handled by `t₂ - t`.
  have hgam_contOn : ContinuousOn gam (Set.Icc (0:ℝ) 1) := by
    intro t ht
    rw [Metric.continuousWithinAt_iff]
    intro ε hε
    have hzA : gam t ∈ A g := gam_mem t
    have hball : gam t ∈ Metric.ball (gam t) ε := Metric.mem_ball_self hε
    obtain ⟨a, haA, hLa, hamin, hleft⟩ := left_Icc_min hg hfib hzA Metric.isOpen_ball hball
    by_cases hcase : L g a < L g (gam t)
    · -- Branch 1: `L a < L (gam t)`.  The window opens on the left.
      obtain ⟨t₁, ht₁, h₁⟩ := exists_lt_gam haA hcase
      by_cases ht1 : t < 1
      · -- Branch 1a: `t < 1`, so `right_Icc` is available.
        have hz1 : gam t ≠ g 1 := by
          intro hcon
          have h2 := gam_lt (t := t) (t' := 1) ht1 ht1 zero_lt_one
          rw [hcon, gam_one] at h2
          exact (lt_irrefl _) h2
        obtain ⟨b, hbA, hLb, hright⟩ := right_Icc hg hfib hzA hz1 Metric.isOpen_ball hball
        obtain ⟨t₂, ht₂, h₂⟩ := exists_gt_gam hbA hLb
        refine ⟨min (t - t₁) (t₂ - t), lt_min (by linarith) (by linarith),
          fun t' ht' hdist => ?_⟩
        have hd : |t' - t| < min (t - t₁) (t₂ - t) := by rwa [Real.dist_eq] at hdist
        have hd1 : t₁ < t' := by
          rw [abs_lt] at hd
          linarith [hd.1, min_le_left (t - t₁) (t₂ - t)]
        have hd2 : t' < t₂ := by
          rw [abs_lt] at hd
          linarith [hd.2, min_le_right (t - t₁) (t₂ - t)]
        rcases lt_trichotomy t' t with hlt | heq | hgt
        · refine Metric.mem_ball.mp (hleft (gam t') (gam_mem t') ?_ (gam_mono (le_of_lt hlt)))
          exact lt_of_lt_of_le h₁ (gam_mono (le_of_lt hd1))
        · subst heq; rw [dist_self]; exact hε
        · refine Metric.mem_ball.mp (hright (gam t') (gam_mem t') (gam_mono (le_of_lt hgt)) ?_)
          exact lt_of_le_of_lt (gam_mono (le_of_lt hd2)) h₂
      · -- Branch 1b: `t = 1`, no `t' > t` in `[0,1]`.
        have ht_eq : t = 1 := le_antisymm ht.2 (le_of_not_gt ht1)
        refine ⟨t - t₁, by linarith, fun t' ht' hdist => ?_⟩
        have hd : |t' - t| < t - t₁ := by rwa [Real.dist_eq] at hdist
        have hd1 : t₁ < t' := by rw [abs_lt] at hd; linarith [hd.1]
        rcases lt_trichotomy t' t with hlt | heq | hgt
        · refine Metric.mem_ball.mp (hleft (gam t') (gam_mem t') ?_ (gam_mono (le_of_lt hlt)))
          exact lt_of_lt_of_le h₁ (gam_mono (le_of_lt hd1))
        · subst heq; rw [dist_self]; exact hε
        · exact absurd ht'.2 (not_le.mpr (by rw [ht_eq] at hgt; exact hgt))
    · -- Branch 2: `L a = L (gam t)`, so `gam t = g 0` and `t = 0`; only the right side is used.
      have hEqL : L g a = L g (gam t) := le_antisymm hLa (le_of_not_gt hcase)
      have hz0 : gam t = g 0 := hamin hEqL
      have ht0 : t = 0 := by
        rcases lt_or_eq_of_le ht.1 with h | h
        · rcases lt_or_eq_of_le ht.2 with h2 | h2
          · have h3 := gam_lt (t := 0) (t' := t) h zero_lt_one h
            rw [gam_zero, hz0] at h3
            exact absurd h3 (lt_irrefl _)
          · rw [h2, gam_one] at hz0
            exact absurd hz0.symm hne
        · exact h.symm
      have hz1' : gam t ≠ g 1 := by rw [hz0]; exact hne
      obtain ⟨b, hbA, hLb, hright⟩ := right_Icc hg hfib hzA hz1' Metric.isOpen_ball hball
      obtain ⟨t₂, ht₂, h₂⟩ := exists_gt_gam hbA hLb
      refine ⟨t₂ - t, by linarith, fun t' ht' hdist => ?_⟩
      have hd : |t' - t| < t₂ - t := by rwa [Real.dist_eq] at hdist
      have hd2 : t' < t₂ := by rw [abs_lt] at hd; linarith [hd.2]
      rcases lt_trichotomy t' t with hlt | heq | hgt
      · rw [ht0] at hlt
        exact absurd ht'.1 (not_le.mpr hlt)
      · subst heq; rw [dist_self]; exact hε
      · refine Metric.mem_ball.mp (hright (gam t') (gam_mem t') (gam_mono (le_of_lt hgt)) ?_)
        exact lt_of_le_of_lt (gam_mono (le_of_lt hd2)) h₂
  have hcont : Continuous γ := by
    have h2 : Continuous ((Set.Icc (0:ℝ) 1).restrict gam) :=
      continuousOn_iff_continuous_restrict.mp hgam_contOn
    have h1 : Continuous (Set.projIcc (0:ℝ) 1 zero_le_one) := continuous_projIcc
    exact h2.comp h1
  exact ⟨γ, hcont, hγinj, hγ0, hγ1⟩

end Work.Topology.PeanoContinuum
