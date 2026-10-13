import Mathlib
import Submission.Work.WilC2.BndDefs

set_option autoImplicit false

namespace Work.WilC2

variable {M : Type} [Field M] [LinearOrder M] [IsStrictOrderedRing M]

/-! ### Boundary points and one-sided neighbourhoods

`IsBnd D x` (see `Work.WilC2.BndDefs`) says that no open interval around `x` is contained in
`D` and none is contained in `Dᶜ`, i.e. `x` is a boundary point of `D` (equivalently of `Dᶜ`).
The next lemmas extract the local information available at a point that is *not* a boundary
point, on the side on which the point lies in the set. -/

/-- Being a boundary point is invariant under taking complements. -/
lemma isBnd_compl {D : Set M} {x : M} : IsBnd Dᶜ x ↔ IsBnd D x := by
  simp only [IsBnd, compl_compl, and_comm]

/-- If `x ∈ D` and `x` is not a boundary point of `D`, then some open interval around `x`
is contained in `D` (`x` is an interior point of `D`). -/
lemma exists_Ioo_subset_of_mem {D : Set M} {x : M} (hxD : x ∈ D) (hx : ¬ IsBnd D x) :
    ∃ ε : M, 0 < ε ∧ Set.Ioo (x - ε) (x + ε) ⊆ D := by
  have hB : ¬ ∃ ε : M, 0 < ε ∧ Set.Ioo (x - ε) (x + ε) ⊆ Dᶜ := by
    rintro ⟨ε, hε, hsub⟩
    exact hsub (mem_Ioo_self hε) hxD
  exact not_not.mp (fun hA => hx ⟨hA, hB⟩)

/-- If `x ∉ D` and `x` is not a boundary point of `D`, then some open interval around `x`
is contained in `Dᶜ`. -/
lemma exists_Ioo_subset_compl_of_notMem {D : Set M} {x : M} (hxD : x ∉ D)
    (hx : ¬ IsBnd D x) : ∃ ε : M, 0 < ε ∧ Set.Ioo (x - ε) (x + ε) ⊆ Dᶜ := by
  have hA : ¬ ∃ ε : M, 0 < ε ∧ Set.Ioo (x - ε) (x + ε) ⊆ D := by
    rintro ⟨ε, hε, hsub⟩
    exact hxD (hsub (mem_Ioo_self hε))
  exact not_not.mp (fun hB => hx ⟨hA, hB⟩)

/-! ### The order-theoretic core

Inside an open interval `(p,q)` in which every point is a non-boundary point of `D`, the set `D`
cannot meet both `D` and its complement with a gap: such a gap would have a "first" point which
is a boundary point of `D`.  The only ingredient beyond the order axioms is the existence of the
relevant suprema, which is exactly what `hsupH` / `hsupHc` provide. -/

/-- There is no point `a ∈ D ∩ (p,q)` strictly below a point `z ∈ (p,q) \ D`, provided all the
points of `(p,q)` are non-boundary points of `D` and the set `D ∩ [u,v]` has a supremum for
every `u < v` with `(D ∩ [u,v]).Nonempty`. -/
lemma false_of_mem_notMem_Ioo {D : Set M} {p q : M}
    (hDsup : ∀ {u v : M}, u < v → (D ∩ Set.Icc u v).Nonempty →
      ∃ s : M, IsLUB (D ∩ Set.Icc u v) s)
    (hnobnd : ∀ x ∈ Set.Ioo p q, ¬ IsBnd D x)
    {a z : M} (haI : a ∈ Set.Ioo p q) (haD : a ∈ D)
    (hzI : z ∈ Set.Ioo p q) (hzD : z ∉ D) (haz : a < z) : False := by
  obtain ⟨s, hs⟩ := hDsup haz ⟨a, haD, Set.left_mem_Icc.mpr haz.le⟩
  have hIcc_sub : Set.Icc a z ⊆ Set.Ioo p q := fun y hy =>
    ⟨lt_of_lt_of_le haI.1 hy.1, lt_of_le_of_lt hy.2 hzI.2⟩
  have hsa : a ≤ s := hs.1 ⟨haD, Set.left_mem_Icc.mpr haz.le⟩
  have hsz : s ≤ z := (isLUB_le_iff hs).mpr (fun y hy => hy.2.2)
  have hsIn : s ∈ Set.Ioo p q := hIcc_sub ⟨hsa, hsz⟩
  by_cases hsD : s ∈ D
  · -- `s ∈ D`: the interval around `s` stays inside `D`, contradicting maximality of `s`
    have hslt : s < z := lt_of_le_of_ne hsz (fun h => hzD (h ▸ hsD))
    obtain ⟨ε, hε, hsub⟩ := exists_Ioo_subset_of_mem hsD (hnobnd s hsIn)
    have hs_lt_min : s < min z (s + ε) := lt_min hslt (by linarith)
    set w : M := (s + min z (s + ε)) / 2 with hwdef
    have hsw : s < w := by rw [hwdef]; linarith
    have hwz : w < z := by
      rw [hwdef]; have := min_le_left z (s + ε); linarith
    have hwse : w < s + ε := by
      rw [hwdef]; have := min_le_right z (s + ε); linarith
    have hwIoo : w ∈ Set.Ioo (s - ε) (s + ε) := ⟨by linarith, hwse⟩
    have hwA : w ∈ D ∩ Set.Icc a z := ⟨hsub hwIoo, ⟨by linarith, le_of_lt hwz⟩⟩
    have := hs.1 hwA
    linarith
  · -- `s ∉ D`: the interval around `s` stays outside `D`, contradicting minimality of `s`
    have hsa' : a < s := lt_of_le_of_ne hsa (fun h => hsD (h ▸ haD))
    obtain ⟨ε, hε, hsub⟩ := exists_Ioo_subset_compl_of_notMem hsD (hnobnd s hsIn)
    have hmax_lt : max a (s - ε) < s := max_lt hsa' (by linarith)
    set w : M := (max a (s - ε) + s) / 2 with hwdef
    have hwlt : w < s := by rw [hwdef]; linarith
    have hwa : a < w := by
      rw [hwdef]; have := le_max_left a (s - ε); linarith
    have hwse : s - ε < w := by
      rw [hwdef]; have := le_max_right a (s - ε); linarith
    have hwIoo : w ∈ Set.Ioo (s - ε) (s + ε) := ⟨hwse, by linarith⟩
    have hw_not_ub : w ∉ upperBounds (D ∩ Set.Icc a z) := fun hub => by
      have := hs.2 hub; linarith
    obtain ⟨y, hyA, hwy⟩ : ∃ y ∈ D ∩ Set.Icc a z, w < y := by
      rw [upperBounds, Set.mem_ofPred_eq] at hw_not_ub
      push Not at hw_not_ub
      exact hw_not_ub
    have hyIoo : y ∈ Set.Ioo (s - ε) (s + ε) :=
      ⟨by linarith, by have := hs.1 hyA; linarith⟩
    exact (hsub hyIoo) hyA.1

/-- If all points of `(p,q)` are non-boundary points of `H` (and of `Hᶜ`), both `H` and `Hᶜ`
admit the suprema used in `false_of_mem_notMem_Ioo`, and `a ∈ H ∩ (p,q)` is nonempty, then
`(p,q) ⊆ H`. -/
lemma Ioo_subset_of_bnd_gap {H : Set M} {p q a : M}
    (haI : a ∈ Set.Ioo p q) (haH : a ∈ H)
    (hnobnd : ∀ x ∈ Set.Ioo p q, ¬ IsBnd H x)
    (hnobndc : ∀ x ∈ Set.Ioo p q, ¬ IsBnd Hᶜ x)
    (hsupH : ∀ {u v : M}, u < v → (H ∩ Set.Icc u v).Nonempty →
      ∃ s : M, IsLUB (H ∩ Set.Icc u v) s)
    (hsupHc : ∀ {u v : M}, u < v → (Hᶜ ∩ Set.Icc u v).Nonempty →
      ∃ s : M, IsLUB (Hᶜ ∩ Set.Icc u v) s) :
    Set.Ioo p q ⊆ H := by
  intro x hxI
  by_contra hxH
  rcases lt_trichotomy a x with hax | hax | hax
  · exact false_of_mem_notMem_Ioo hsupH hnobnd haI haH hxI hxH hax
  · exact absurd (hax ▸ haH) hxH
  · exact false_of_mem_notMem_Ioo hsupHc hnobndc hxI hxH haI (by simpa using haH) hax

/-- `gap_subset_of_bnd`: if `b ∈ H` is not a boundary point of `H`, if no boundary point of `H`
lies strictly between `c` and `b`, and if `H` and `Hᶜ` admit suprema of their traces on the
bounded closed intervals, then the whole closed interval between `c` and `b` is contained in
`H`. -/
theorem gap_subset_of_bnd
    {M : Type} [Field M] [LinearOrder M] [IsStrictOrderedRing M]
    {H F : Set M} {b c : M}
    (hbH : b ∈ H) (hbn : ¬ Work.WilC2.IsBnd H b) (hcF : c ∉ F)
    (hFbd : ∀ x : M, Work.WilC2.IsBnd H x → x ∈ F)
    (hgap : ∀ f ∈ F, ¬ ((c < f ∧ f < b) ∨ (b < f ∧ f < c)))
    (hsupH : ∀ {u v : M}, u < v → (H ∩ Set.Icc u v).Nonempty →
      ∃ s : M, IsLUB (H ∩ Set.Icc u v) s)
    (hsupHc : ∀ {u v : M}, u < v → (Hᶜ ∩ Set.Icc u v).Nonempty →
      ∃ s : M, IsLUB (Hᶜ ∩ Set.Icc u v) s) :
    Set.Icc (min c b) (max c b) ⊆ H := by
  -- `b ∈ H` is an interior point of `H`: some interval around `b` lies in `H`
  obtain ⟨δ, hδ, hδsub⟩ := exists_Ioo_subset_of_mem hbH hbn
  -- `c` is not a boundary point of `H`
  have hcnotbnd : ¬ IsBnd H c := fun h => hcF (hFbd c h)
  rcases lt_trichotomy c b with hlt | heq | hgt
  · -- case `c < b`: the interval is `Icc c b`
    rw [min_eq_left hlt.le, max_eq_right hlt.le]
    -- a point `a ∈ H ∩ (c,b)`
    set m : M := min δ (b - c) with hmdef
    have hmpos : 0 < m := by rw [hmdef]; exact lt_min hδ (by linarith)
    have hmleδ : m ≤ δ := min_le_left _ _
    have hmleb : m ≤ b - c := min_le_right _ _
    set a : M := b - m / 2 with hadef
    have ha_lt_b : a < b := by rw [hadef]; linarith
    have hc_lt_a : c < a := by rw [hadef]; linarith
    have ha_neigh : a ∈ Set.Ioo (b - δ) (b + δ) := by
      rw [hadef]; exact ⟨by have := hmleδ; linarith, by linarith⟩
    have haH : a ∈ H := hδsub ha_neigh
    -- no point of `(c,b)` is a boundary point of `H`
    have hnobnd : ∀ x ∈ Set.Ioo c b, ¬ IsBnd H x := by
      intro x hx hxb
      exact hgap x (hFbd x hxb) (Or.inl ⟨hx.1, hx.2⟩)
    have hIoo : Set.Ioo c b ⊆ H :=
      Ioo_subset_of_bnd_gap ⟨hc_lt_a, ha_lt_b⟩ haH hnobnd
        (fun x hx => by rw [isBnd_compl]; exact hnobnd x hx)
        hsupH hsupHc
    -- `c ∈ H`
    have hcH : c ∈ H := by
      by_contra hcH'
      obtain ⟨ε, hε, hεsub⟩ := exists_Ioo_subset_compl_of_notMem hcH' hcnotbnd
      set m' : M := min ε (b - c) with hm'def
      have hm'pos : 0 < m' := by rw [hm'def]; exact lt_min hε (by linarith)
      have hm'leε : m' ≤ ε := min_le_left _ _
      have hm'leb : m' ≤ b - c := min_le_right _ _
      set w : M := c + m' / 2 with hwdef
      have hcw : c < w := by rw [hwdef]; linarith
      have hwb : w < b := by rw [hwdef]; linarith
      have hwH : w ∈ H := hIoo ⟨hcw, hwb⟩
      have hwHc : w ∈ Hᶜ := hεsub ⟨by rw [hwdef]; linarith, by rw [hwdef]; linarith⟩
      exact hwHc hwH
    intro x hx
    rw [Set.mem_Icc] at hx
    by_cases hxc : x = c
    · rw [hxc]; exact hcH
    by_cases hxb : x = b
    · rw [hxb]; exact hbH
    · exact hIoo ⟨lt_of_le_of_ne hx.1 (Ne.symm hxc), lt_of_le_of_ne hx.2 hxb⟩
  · -- case `c = b`: the interval is the singleton `{c} = {b}`
    rw [heq]
    simp only [min_self, max_self]
    intro x hx
    rw [Set.Icc_self, Set.mem_singleton_iff] at hx
    rw [hx]
    exact hbH
  · -- case `b < c`: the interval is `Icc b c`
    rw [min_eq_right hgt.le, max_eq_left hgt.le]
    -- a point `a ∈ H ∩ (b,c)`
    set m : M := min δ (c - b) with hmdef
    have hmpos : 0 < m := by rw [hmdef]; exact lt_min hδ (by linarith)
    have hmleδ : m ≤ δ := min_le_left _ _
    have hmlec : m ≤ c - b := min_le_right _ _
    set a : M := b + m / 2 with hadef
    have hb_lt_a : b < a := by rw [hadef]; linarith
    have ha_lt_c : a < c := by rw [hadef]; linarith
    have ha_neigh : a ∈ Set.Ioo (b - δ) (b + δ) := by
      rw [hadef]; exact ⟨by linarith, by have := hmleδ; linarith⟩
    have haH : a ∈ H := hδsub ha_neigh
    -- no point of `(b,c)` is a boundary point of `H`
    have hnobnd : ∀ x ∈ Set.Ioo b c, ¬ IsBnd H x := by
      intro x hx hxb
      exact hgap x (hFbd x hxb) (Or.inr ⟨hx.1, hx.2⟩)
    have hIoo : Set.Ioo b c ⊆ H :=
      Ioo_subset_of_bnd_gap (p := b) (q := c) ⟨hb_lt_a, ha_lt_c⟩ haH hnobnd
        (fun x hx => by rw [isBnd_compl]; exact hnobnd x hx)
        hsupH hsupHc
    -- `c ∈ H`
    have hcH : c ∈ H := by
      by_contra hcH'
      obtain ⟨ε, hε, hεsub⟩ := exists_Ioo_subset_compl_of_notMem hcH' hcnotbnd
      set m' : M := min ε (c - b) with hm'def
      have hm'pos : 0 < m' := by rw [hm'def]; exact lt_min hε (by linarith)
      have hm'leε : m' ≤ ε := min_le_left _ _
      have hm'leb : m' ≤ c - b := min_le_right _ _
      set w : M := c - m' / 2 with hwdef
      have hbw : b < w := by rw [hwdef]; linarith
      have hwc : w < c := by rw [hwdef]; linarith
      have hwH : w ∈ H := hIoo ⟨hbw, hwc⟩
      have hwHc : w ∈ Hᶜ := hεsub ⟨by rw [hwdef]; linarith, by rw [hwdef]; linarith⟩
      exact hwHc hwH
    intro x hx
    rw [Set.mem_Icc] at hx
    by_cases hxb : x = b
    · rw [hxb]; exact hbH
    by_cases hxc : x = c
    · rw [hxc]; exact hcH
    · exact hIoo ⟨lt_of_le_of_ne hx.1 (Ne.symm hxb), lt_of_le_of_ne hx.2 hxc⟩

end Work.WilC2
