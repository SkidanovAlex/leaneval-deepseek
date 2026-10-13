/-
  WilC4 : `germ_cover` — the one-sided strict-germ dichotomy for a definable functional set.

  If the partial function encoded by `Y ⊆ ℝ²` is single-valued (`hfun`), the germ dichotomy
  `hgem` holds for finite unions of order-connected subsets of `ℝ` (this is a theorem of `ℝ`,
  and is supplied by o-minimality in the applications), the fibres `MonoLset Y x` and
  `MonoHset Y x` are finite unions of order-connected sets (`hLset`, `hHset`), and a point
  `x ∈ (a,b)` of the domain interval is *not* locally constant (`hW`), then the left germ and
  the right germ of `Y` at `x` are each *strictly* below or *strictly* above the value at `x`:

    `x ∈ MonoLm Y ∨ x ∈ MonoHm Y`   and   `x ∈ MonoLp Y ∨ x ∈ MonoHp Y`.

  The two sides are proved independently.  On the left, `hgem` applied to `MonoLset Y x` gives
  either a left-neighbourhood contained in it (whence `MonoLm`) or one disjoint from it; in the
  latter case `hgem` applied to `MonoHset Y x` likewise gives either `MonoHm` or a
  left-neighbourhood on which the value of the function is pinned to the value at `x`.  But any
  point of such a one-sided interval has a *two-sided* neighbourhood (contained in the interval,
  hence inside `(a,b) ⊆ MonoDom Y`) on which the value is constant, i.e. lies in `MonoW Y`,
  contradicting `hW`.
-/
import Mathlib
import Submission.Work.WilC4.monoDefs

set_option autoImplicit false

noncomputable section

namespace Work.WilC4

/-- `S ⊆ ℝ` is a finite union of order-connected subsets of `ℝ`. -/
private def GemProp (S : Set ℝ) : Prop :=
  ∃ s : Finset (Set ℝ), (∀ I ∈ s, I.OrdConnected) ∧ S = ⋃₀ (s : Set (Set ℝ))

/-- The **left germ dichotomy** of `S` at `x`: `S` contains a left-neighbourhood of `x`, or
avoids one. -/
private def LeftDich (S : Set ℝ) (x : ℝ) : Prop :=
  (∃ ε : ℝ, 0 < ε ∧ Set.Ioo (x - ε) x ⊆ S) ∨
    (∃ ε : ℝ, 0 < ε ∧ ∀ z ∈ Set.Ioo (x - ε) x, z ∉ S)

/-- The **right germ dichotomy** of `S` at `x`. -/
private def RightDich (S : Set ℝ) (x : ℝ) : Prop :=
  (∃ ε : ℝ, 0 < ε ∧ Set.Ioo x (x + ε) ⊆ S) ∨
    (∃ ε : ℝ, 0 < ε ∧ ∀ z ∈ Set.Ioo x (x + ε), z ∉ S)

/-- The germ-dichotomy hypothesis of `germ_cover`, in the vocabulary above. -/
private def GemHyp : Prop := ∀ (S : Set ℝ), GemProp S → ∀ x : ℝ, LeftDich S x ∧ RightDich S x

variable {Y : Set (Fin 2 → ℝ)}

/-- If the left germ at `x` is neither strictly below nor strictly above the value `y₀` of the
function at `x`, then `y₀` is the *only* value of the function on a whole left-neighbourhood
of `x` (restricted to the domain). -/
private lemma germ_left_of_not {x y₀ : ℝ}
    (hfun : ∀ x y y' : ℝ, ![x, y] ∈ Y → ![x, y'] ∈ Y → y = y')
    (hgem : GemHyp)
    (hLset : ∀ x : ℝ, ∃ s : Finset (Set ℝ),
      (∀ I ∈ s, I.OrdConnected) ∧ MonoLset Y x = ⋃₀ (s : Set (Set ℝ)))
    (hHset : ∀ x : ℝ, ∃ s : Finset (Set ℝ),
      (∀ I ∈ s, I.OrdConnected) ∧ MonoHset Y x = ⋃₀ (s : Set (Set ℝ)))
    (hy₀ : ![x, y₀] ∈ Y) (hL : x ∉ MonoLm Y) (hH : x ∉ MonoHm Y) :
    ∃ ε : ℝ, 0 < ε ∧ ∀ z ∈ Set.Ioo (x - ε) x, z ∈ MonoDom Y → ![z, y₀] ∈ Y := by
  obtain ⟨h1, _⟩ := hgem (MonoLset Y x) (hLset x) x
  obtain ⟨h2, _⟩ := hgem (MonoHset Y x) (hHset x) x
  -- on the left, a neighbourhood inside `MonoLset Y x` would give `MonoLm`
  have hLdisj : ∃ ε : ℝ, 0 < ε ∧ ∀ z ∈ Set.Ioo (x - ε) x, z ∉ MonoLset Y x := by
    rcases h1 with ⟨ε, hε, hsub⟩ | h
    · exfalso
      apply hL
      rw [mem_MonoLm]
      refine ⟨ε, y₀, hε, hy₀, ?_⟩
      intro z hz1 hz2
      have hzS : z ∈ MonoLset Y x := hsub (Set.mem_Ioo.mpr ⟨hz1, hz2⟩)
      simp only [mem_MonoLset] at hzS
      obtain ⟨y, y', hyz, hxy', hyy'⟩ := hzS
      exact ⟨y, hyz, by rw [hfun x y' y₀ hxy' hy₀] at hyy'; exact hyy'⟩
    · exact h
  -- on the left, a neighbourhood inside `MonoHset Y x` would give `MonoHm`
  have hHdisj : ∃ ε : ℝ, 0 < ε ∧ ∀ z ∈ Set.Ioo (x - ε) x, z ∉ MonoHset Y x := by
    rcases h2 with ⟨ε, hε, hsub⟩ | h
    · exfalso
      apply hH
      rw [mem_MonoHm]
      refine ⟨ε, y₀, hε, hy₀, ?_⟩
      intro z hz1 hz2
      have hzS : z ∈ MonoHset Y x := hsub (Set.mem_Ioo.mpr ⟨hz1, hz2⟩)
      simp only [mem_MonoHset] at hzS
      obtain ⟨y, y', hyz, hxy', hyy'⟩ := hzS
      exact ⟨y, hyz, by rw [hfun x y' y₀ hxy' hy₀] at hyy'; exact hyy'⟩
    · exact h
  obtain ⟨ε₁, hε₁, hD₁⟩ := hLdisj
  obtain ⟨ε₂, hε₂, hD₂⟩ := hHdisj
  refine ⟨min ε₁ ε₂, lt_min hε₁ hε₂, ?_⟩
  intro z hz hzdom
  -- `z` is neither below nor above `x`, so its value (which exists inside the domain) is `y₀`
  have hz₁ : z ∈ Set.Ioo (x - ε₁) x :=
    Set.mem_Ioo.mpr ⟨by have h := hz.1; have h' := min_le_left ε₁ ε₂; linarith, hz.2⟩
  have hz₂ : z ∈ Set.Ioo (x - ε₂) x :=
    Set.mem_Ioo.mpr ⟨by have h := hz.1; have h' := min_le_right ε₁ ε₂; linarith, hz.2⟩
  obtain ⟨y, hy⟩ := hzdom
  have hnot1 := hD₁ z hz₁
  have hnot2 := hD₂ z hz₂
  have hA : y₀ ≤ y :=
    not_lt.mp (fun hlt => hnot1 (by simp only [mem_MonoLset]; exact ⟨y, y₀, hy, hy₀, hlt⟩))
  have hB : y ≤ y₀ :=
    not_lt.mp (fun hlt => hnot2 (by simp only [mem_MonoHset]; exact ⟨y, y₀, hy, hy₀, hlt⟩))
  have hyz : y = y₀ := le_antisymm hB hA
  rw [← hyz]
  exact hy

/-- The right-germ version of `germ_left_of_not`. -/
private lemma germ_right_of_not {x y₀ : ℝ}
    (hfun : ∀ x y y' : ℝ, ![x, y] ∈ Y → ![x, y'] ∈ Y → y = y')
    (hgem : GemHyp)
    (hLset : ∀ x : ℝ, ∃ s : Finset (Set ℝ),
      (∀ I ∈ s, I.OrdConnected) ∧ MonoLset Y x = ⋃₀ (s : Set (Set ℝ)))
    (hHset : ∀ x : ℝ, ∃ s : Finset (Set ℝ),
      (∀ I ∈ s, I.OrdConnected) ∧ MonoHset Y x = ⋃₀ (s : Set (Set ℝ)))
    (hy₀ : ![x, y₀] ∈ Y) (hL : x ∉ MonoLp Y) (hH : x ∉ MonoHp Y) :
    ∃ ε : ℝ, 0 < ε ∧ ∀ z ∈ Set.Ioo x (x + ε), z ∈ MonoDom Y → ![z, y₀] ∈ Y := by
  obtain ⟨_, h1⟩ := hgem (MonoLset Y x) (hLset x) x
  obtain ⟨_, h2⟩ := hgem (MonoHset Y x) (hHset x) x
  have hLdisj : ∃ ε : ℝ, 0 < ε ∧ ∀ z ∈ Set.Ioo x (x + ε), z ∉ MonoLset Y x := by
    rcases h1 with ⟨ε, hε, hsub⟩ | h
    · exfalso
      apply hL
      rw [mem_MonoLp]
      refine ⟨ε, y₀, hε, hy₀, ?_⟩
      intro z hz1 hz2
      have hzS : z ∈ MonoLset Y x := hsub (Set.mem_Ioo.mpr ⟨hz1, hz2⟩)
      simp only [mem_MonoLset] at hzS
      obtain ⟨y, y', hyz, hxy', hyy'⟩ := hzS
      exact ⟨y, hyz, by rw [hfun x y' y₀ hxy' hy₀] at hyy'; exact hyy'⟩
    · exact h
  have hHdisj : ∃ ε : ℝ, 0 < ε ∧ ∀ z ∈ Set.Ioo x (x + ε), z ∉ MonoHset Y x := by
    rcases h2 with ⟨ε, hε, hsub⟩ | h
    · exfalso
      apply hH
      rw [mem_MonoHp]
      refine ⟨ε, y₀, hε, hy₀, ?_⟩
      intro z hz1 hz2
      have hzS : z ∈ MonoHset Y x := hsub (Set.mem_Ioo.mpr ⟨hz1, hz2⟩)
      simp only [mem_MonoHset] at hzS
      obtain ⟨y, y', hyz, hxy', hyy'⟩ := hzS
      exact ⟨y, hyz, by rw [hfun x y' y₀ hxy' hy₀] at hyy'; exact hyy'⟩
    · exact h
  obtain ⟨ε₁, hε₁, hD₁⟩ := hLdisj
  obtain ⟨ε₂, hε₂, hD₂⟩ := hHdisj
  refine ⟨min ε₁ ε₂, lt_min hε₁ hε₂, ?_⟩
  intro z hz hzdom
  have hz₁ : z ∈ Set.Ioo x (x + ε₁) :=
    Set.mem_Ioo.mpr ⟨hz.1, by have h := hz.2; have h' := min_le_left ε₁ ε₂; linarith⟩
  have hz₂ : z ∈ Set.Ioo x (x + ε₂) :=
    Set.mem_Ioo.mpr ⟨hz.1, by have h := hz.2; have h' := min_le_right ε₁ ε₂; linarith⟩
  obtain ⟨y, hy⟩ := hzdom
  have hnot1 := hD₁ z hz₁
  have hnot2 := hD₂ z hz₂
  have hA : y₀ ≤ y :=
    not_lt.mp (fun hlt => hnot1 (by simp only [mem_MonoLset]; exact ⟨y, y₀, hy, hy₀, hlt⟩))
  have hB : y ≤ y₀ :=
    not_lt.mp (fun hlt => hnot2 (by simp only [mem_MonoHset]; exact ⟨y, y₀, hy, hy₀, hlt⟩))
  have hyz : y = y₀ := le_antisymm hB hA
  rw [← hyz]
  exact hy

/-- **Left half** of `germ_cover`: if the left germ at `x ∈ (a,b)` were neither strictly below
nor strictly above, we would get a point of `(a,b)` that is locally constant. -/
private lemma left_contra {a b x : ℝ}
    (hfun : ∀ x y y' : ℝ, ![x, y] ∈ Y → ![x, y'] ∈ Y → y = y')
    (hgem : GemHyp)
    (hLset : ∀ x : ℝ, ∃ s : Finset (Set ℝ),
      (∀ I ∈ s, I.OrdConnected) ∧ MonoLset Y x = ⋃₀ (s : Set (Set ℝ)))
    (hHset : ∀ x : ℝ, ∃ s : Finset (Set ℝ),
      (∀ I ∈ s, I.OrdConnected) ∧ MonoHset Y x = ⋃₀ (s : Set (Set ℝ)))
    (hDom : Set.Ioo a b ⊆ MonoDom Y) (hW : ∀ x ∈ Set.Ioo a b, x ∉ MonoW Y)
    (hx : x ∈ Set.Ioo a b) (hL : x ∉ MonoLm Y) (hH : x ∉ MonoHm Y) : False := by
  obtain ⟨y₀, hy₀⟩ := hDom hx
  obtain ⟨ε, hε, hεp⟩ := germ_left_of_not hfun hgem hLset hHset hy₀ hL hH
  have hax : a < x := hx.1
  have hxb : x < b := hx.2
  -- a point of `(a,b)` inside the left-neighbourhood
  have hminpos : 0 < min ε (x - a) := lt_min hε (by linarith)
  set z := x - min ε (x - a) / 2 with hzdef
  have hzlt : z < x := by rw [hzdef]; linarith
  have hza : a < z := by rw [hzdef]; have := min_le_right ε (x - a); linarith
  have hzε : x - ε < z := by rw [hzdef]; have := min_le_left ε (x - a); linarith
  have hz_ab : z ∈ Set.Ioo a b := Set.mem_Ioo.mpr ⟨hza, by linarith⟩
  have hz_left : z ∈ Set.Ioo (x - ε) x := Set.mem_Ioo.mpr ⟨hzε, hzlt⟩
  have hzy : ![z, y₀] ∈ Y := hεp z hz_left (hDom hz_ab)
  -- a two-sided neighbourhood of `z`, still inside `(a,b)` and inside the left-neighbourhood
  have hopen : IsOpen (Set.Ioo (x - ε) x ∩ Set.Ioo a b) := isOpen_Ioo.inter isOpen_Ioo
  have hzU : z ∈ Set.Ioo (x - ε) x ∩ Set.Ioo a b := ⟨hz_left, hz_ab⟩
  obtain ⟨η, hη, hball⟩ := Metric.isOpen_iff.mp hopen z hzU
  have hWz : z ∈ MonoW Y := by
    rw [mem_MonoW]
    refine ⟨y₀, η, hη, hzy, ?_⟩
    intro z' hz'1 hz'2
    have hz'ball : z' ∈ Metric.ball z η := by
      rw [Metric.mem_ball, Real.dist_eq, abs_sub_lt_iff]
      exact ⟨by linarith, by linarith⟩
    have hU := hball hz'ball
    exact hεp z' hU.1 (hDom hU.2)
  exact (hW z hz_ab) hWz

/-- **Right half** of `germ_cover`. -/
private lemma right_contra {a b x : ℝ}
    (hfun : ∀ x y y' : ℝ, ![x, y] ∈ Y → ![x, y'] ∈ Y → y = y')
    (hgem : GemHyp)
    (hLset : ∀ x : ℝ, ∃ s : Finset (Set ℝ),
      (∀ I ∈ s, I.OrdConnected) ∧ MonoLset Y x = ⋃₀ (s : Set (Set ℝ)))
    (hHset : ∀ x : ℝ, ∃ s : Finset (Set ℝ),
      (∀ I ∈ s, I.OrdConnected) ∧ MonoHset Y x = ⋃₀ (s : Set (Set ℝ)))
    (hDom : Set.Ioo a b ⊆ MonoDom Y) (hW : ∀ x ∈ Set.Ioo a b, x ∉ MonoW Y)
    (hx : x ∈ Set.Ioo a b) (hL : x ∉ MonoLp Y) (hH : x ∉ MonoHp Y) : False := by
  obtain ⟨y₀, hy₀⟩ := hDom hx
  obtain ⟨ε, hε, hεp⟩ := germ_right_of_not hfun hgem hLset hHset hy₀ hL hH
  have hax : a < x := hx.1
  have hxb : x < b := hx.2
  have hminpos : 0 < min ε (b - x) := lt_min hε (by linarith)
  set z := x + min ε (b - x) / 2 with hzdef
  have hzgt : x < z := by rw [hzdef]; linarith
  have hzb : z < b := by rw [hzdef]; have := min_le_right ε (b - x); linarith
  have hzε : z < x + ε := by rw [hzdef]; have := min_le_left ε (b - x); linarith
  have hz_ab : z ∈ Set.Ioo a b := Set.mem_Ioo.mpr ⟨by linarith, hzb⟩
  have hz_right : z ∈ Set.Ioo x (x + ε) := Set.mem_Ioo.mpr ⟨hzgt, hzε⟩
  have hzy : ![z, y₀] ∈ Y := hεp z hz_right (hDom hz_ab)
  have hopen : IsOpen (Set.Ioo x (x + ε) ∩ Set.Ioo a b) := isOpen_Ioo.inter isOpen_Ioo
  have hzU : z ∈ Set.Ioo x (x + ε) ∩ Set.Ioo a b := ⟨hz_right, hz_ab⟩
  obtain ⟨η, hη, hball⟩ := Metric.isOpen_iff.mp hopen z hzU
  have hWz : z ∈ MonoW Y := by
    rw [mem_MonoW]
    refine ⟨y₀, η, hη, hzy, ?_⟩
    intro z' hz'1 hz'2
    have hz'ball : z' ∈ Metric.ball z η := by
      rw [Metric.mem_ball, Real.dist_eq, abs_sub_lt_iff]
      exact ⟨by linarith, by linarith⟩
    have hU := hball hz'ball
    exact hεp z' hU.1 (hDom hU.2)
  exact (hW z hz_ab) hWz

theorem germ_cover {Y : Set (Fin 2 → ℝ)} {a b : ℝ}
    (hfun : ∀ x y y' : ℝ, ![x, y] ∈ Y → ![x, y'] ∈ Y → y = y')
    (hgem : ∀ (S : Set ℝ),
      (∃ s : Finset (Set ℝ), (∀ I ∈ s, I.OrdConnected) ∧ S = ⋃₀ (s : Set (Set ℝ))) →
      ∀ x : ℝ,
        ((∃ ε : ℝ, 0 < ε ∧ Set.Ioo (x - ε) x ⊆ S) ∨
          (∃ ε : ℝ, 0 < ε ∧ ∀ z ∈ Set.Ioo (x - ε) x, z ∉ S)) ∧
        ((∃ ε : ℝ, 0 < ε ∧ Set.Ioo x (x + ε) ⊆ S) ∨
          (∃ ε : ℝ, 0 < ε ∧ ∀ z ∈ Set.Ioo x (x + ε), z ∉ S)))
    (hLset : ∀ x : ℝ, ∃ s : Finset (Set ℝ),
      (∀ I ∈ s, I.OrdConnected) ∧ MonoLset Y x = ⋃₀ (s : Set (Set ℝ)))
    (hHset : ∀ x : ℝ, ∃ s : Finset (Set ℝ),
      (∀ I ∈ s, I.OrdConnected) ∧ MonoHset Y x = ⋃₀ (s : Set (Set ℝ)))
    (hDom : Set.Ioo a b ⊆ MonoDom Y) (hW : ∀ x ∈ Set.Ioo a b, x ∉ MonoW Y)
    {x : ℝ} (hx : x ∈ Set.Ioo a b) :
    (x ∈ MonoLm Y ∨ x ∈ MonoHm Y) ∧ (x ∈ MonoLp Y ∨ x ∈ MonoHp Y) := by
  refine ⟨?_, ?_⟩
  · by_contra hc
    rw [not_or] at hc
    exact left_contra hfun hgem hLset hHset hDom hW hx hc.1 hc.2
  · by_contra hc
    rw [not_or] at hc
    exact right_contra hfun hgem hLset hHset hDom hW hx hc.1 hc.2

end Work.WilC4
