import Mathlib
import Submission.Work.WilC4.CritDefs
import Submission.Work.WilC4.UnifDefs
import Submission.Work.WilC4.germ_cover
import Submission.Work.WilC4.germ_mono_of_types
import Submission.Work.WilC4.germ_extr
import Submission.Work.WilC4.finUnionOrd_germ
import Submission.Work.WilC4.monoDefs
import Submission.Work.WilC4.mono_real
import Submission.Work.WilC4.ParamMonoDefs

set_option autoImplicit false
set_option maxHeartbeats 1000000
noncomputable section
open Classical FirstOrder FirstOrder.Language
namespace Work.WilC4
open WilkiesDesign WilkiesDesign.CG

variable {k : ℕ}

/-! ## Helpers: the fibre relation -/

lemma cfib_fun {Y : Set (Fin (k + 2) → ℝ)} {c : Fin k → ℝ}
    (hfun : ∀ (c : Fin k → ℝ) (x y y' : ℝ), CGr Y c x y → CGr Y c x y' → y = y') :
    ∀ x y y' : ℝ, ![x, y] ∈ Cfib Y c → ![x, y'] ∈ Cfib Y c → y = y' := by
  intro x y y' h1 h2
  rw [mem_cfib_cons] at h1 h2
  exact hfun c x y y' h1 h2

@[simp] lemma mem_pMonoLm_cons {Y : Set (Fin (k + 2) → ℝ)} {c : Fin k → ℝ} {x : ℝ} :
    Fin.cons x c ∈ PMonoLm Y ↔ x ∈ MonoLm (Cfib Y c) := by
  simp only [PMonoLm, Set.mem_setOf_eq, tup_cons, Fin.cons_zero]

@[simp] lemma mem_pMonoHm_cons {Y : Set (Fin (k + 2) → ℝ)} {c : Fin k → ℝ} {x : ℝ} :
    Fin.cons x c ∈ PMonoHm Y ↔ x ∈ MonoHm (Cfib Y c) := by
  simp only [PMonoHm, Set.mem_setOf_eq, tup_cons, Fin.cons_zero]

@[simp] lemma mem_pMonoLp_cons {Y : Set (Fin (k + 2) → ℝ)} {c : Fin k → ℝ} {x : ℝ} :
    Fin.cons x c ∈ PMonoLp Y ↔ x ∈ MonoLp (Cfib Y c) := by
  simp only [PMonoLp, Set.mem_setOf_eq, tup_cons, Fin.cons_zero]

@[simp] lemma mem_pMonoHp_cons {Y : Set (Fin (k + 2) → ℝ)} {c : Fin k → ℝ} {x : ℝ} :
    Fin.cons x c ∈ PMonoHp Y ↔ x ∈ MonoHp (Cfib Y c) := by
  simp only [PMonoHp, Set.mem_setOf_eq, tup_cons, Fin.cons_zero]

/-! ## Bad data -/

lemma badRU_data {Y : Set (Fin (k + 2) → ℝ)} {c : Fin k → ℝ} {u v x : ℝ}
    (hbad : ∀ x : ℝ, u < x → x < v → Fin.cons x c ∈ BadRU Y) (hx : u < x) (hxv : x < v) :
    ∃ ε δ y : ℝ, 0 < ε ∧ 0 < δ ∧ CGr Y c x y ∧
      (∀ t : ℝ, x - δ < t → t < x + δ → ∃ w : ℝ, CGr Y c t w) ∧
      (∀ t : ℝ, x < t → t < x + δ → ∀ w : ℝ, CGr Y c t w → y + ε ≤ w) := by
  have h := hbad x hx hxv
  simp only [BadRU, Set.mem_setOf_eq, tup_cons, Fin.cons_zero] at h
  obtain ⟨hint, ε, δ, y, hε, hδ, hxy, hjm⟩ := h
  simp only [IntDom] at hint
  obtain ⟨δ₀, hδ₀, hδ₀'⟩ := hint
  exact ⟨ε, min δ₀ δ, y, hε, lt_min hδ₀ hδ, hxy,
    fun t ht1 ht2 => hδ₀' t (by linarith [min_le_left δ₀ δ]) (by linarith [min_le_left δ₀ δ]),
    fun t ht1 ht2 w hw => hjm t ht1 (by linarith [min_le_right δ₀ δ]) w hw⟩

lemma badRD_data {Y : Set (Fin (k + 2) → ℝ)} {c : Fin k → ℝ} {u v x : ℝ}
    (hbad : ∀ x : ℝ, u < x → x < v → Fin.cons x c ∈ BadRD Y) (hx : u < x) (hxv : x < v) :
    ∃ ε δ y : ℝ, 0 < ε ∧ 0 < δ ∧ CGr Y c x y ∧
      (∀ t : ℝ, x - δ < t → t < x + δ → ∃ w : ℝ, CGr Y c t w) ∧
      (∀ t : ℝ, x < t → t < x + δ → ∀ w : ℝ, CGr Y c t w → w + ε ≤ y) := by
  have h := hbad x hx hxv
  simp only [BadRD, Set.mem_setOf_eq, tup_cons, Fin.cons_zero] at h
  obtain ⟨hint, ε, δ, y, hε, hδ, hxy, hjm⟩ := h
  simp only [IntDom] at hint
  obtain ⟨δ₀, hδ₀, hδ₀'⟩ := hint
  exact ⟨ε, min δ₀ δ, y, hε, lt_min hδ₀ hδ, hxy,
    fun t ht1 ht2 => hδ₀' t (by linarith [min_le_left δ₀ δ]) (by linarith [min_le_left δ₀ δ]),
    fun t ht1 ht2 w hw => hjm t ht1 (by linarith [min_le_right δ₀ δ]) w hw⟩

lemma badLU_data {Y : Set (Fin (k + 2) → ℝ)} {c : Fin k → ℝ} {u v x : ℝ}
    (hbad : ∀ x : ℝ, u < x → x < v → Fin.cons x c ∈ BadLU Y) (hx : u < x) (hxv : x < v) :
    ∃ ε δ y : ℝ, 0 < ε ∧ 0 < δ ∧ CGr Y c x y ∧
      (∀ t : ℝ, x - δ < t → t < x + δ → ∃ w : ℝ, CGr Y c t w) ∧
      (∀ t : ℝ, x - δ < t → t < x → ∀ w : ℝ, CGr Y c t w → y + ε ≤ w) := by
  have h := hbad x hx hxv
  simp only [BadLU, Set.mem_setOf_eq, tup_cons, Fin.cons_zero] at h
  obtain ⟨hint, ε, δ, y, hε, hδ, hxy, hjm⟩ := h
  simp only [IntDom] at hint
  obtain ⟨δ₀, hδ₀, hδ₀'⟩ := hint
  exact ⟨ε, min δ₀ δ, y, hε, lt_min hδ₀ hδ, hxy,
    fun t ht1 ht2 => hδ₀' t (by linarith [min_le_left δ₀ δ]) (by linarith [min_le_left δ₀ δ]),
    fun t ht1 ht2 w hw => hjm t (by linarith [min_le_right δ₀ δ]) ht2 w hw⟩

lemma badLD_data {Y : Set (Fin (k + 2) → ℝ)} {c : Fin k → ℝ} {u v x : ℝ}
    (hbad : ∀ x : ℝ, u < x → x < v → Fin.cons x c ∈ BadLD Y) (hx : u < x) (hxv : x < v) :
    ∃ ε δ y : ℝ, 0 < ε ∧ 0 < δ ∧ CGr Y c x y ∧
      (∀ t : ℝ, x - δ < t → t < x + δ → ∃ w : ℝ, CGr Y c t w) ∧
      (∀ t : ℝ, x - δ < t → t < x → ∀ w : ℝ, CGr Y c t w → w + ε ≤ y) := by
  have h := hbad x hx hxv
  simp only [BadLD, Set.mem_setOf_eq, tup_cons, Fin.cons_zero] at h
  obtain ⟨hint, ε, δ, y, hε, hδ, hxy, hjm⟩ := h
  simp only [IntDom] at hint
  obtain ⟨δ₀, hδ₀, hδ₀'⟩ := hint
  exact ⟨ε, min δ₀ δ, y, hε, lt_min hδ₀ hδ, hxy,
    fun t ht1 ht2 => hδ₀' t (by linarith [min_le_left δ₀ δ]) (by linarith [min_le_left δ₀ δ]),
    fun t ht1 ht2 w hw => hjm t (by linarith [min_le_right δ₀ δ]) ht2 w hw⟩

/-! ## Domain and locally-constant exclusion -/

lemma monoDom_of_badRU {Y : Set (Fin (k + 2) → ℝ)} {c : Fin k → ℝ} {u v : ℝ}
    (hbad : ∀ x : ℝ, u < x → x < v → Fin.cons x c ∈ BadRU Y) :
    Set.Ioo u v ⊆ MonoDom (Cfib Y c) := by
  intro x hx
  obtain ⟨ε, δ, y, -, -, hxy, -, -⟩ := badRU_data hbad hx.1 hx.2
  exact ⟨y, mem_cfib_cons.mpr hxy⟩

lemma monoDom_of_badRD {Y : Set (Fin (k + 2) → ℝ)} {c : Fin k → ℝ} {u v : ℝ}
    (hbad : ∀ x : ℝ, u < x → x < v → Fin.cons x c ∈ BadRD Y) :
    Set.Ioo u v ⊆ MonoDom (Cfib Y c) := by
  intro x hx
  obtain ⟨ε, δ, y, -, -, hxy, -, -⟩ := badRD_data hbad hx.1 hx.2
  exact ⟨y, mem_cfib_cons.mpr hxy⟩

lemma monoDom_of_badLU {Y : Set (Fin (k + 2) → ℝ)} {c : Fin k → ℝ} {u v : ℝ}
    (hbad : ∀ x : ℝ, u < x → x < v → Fin.cons x c ∈ BadLU Y) :
    Set.Ioo u v ⊆ MonoDom (Cfib Y c) := by
  intro x hx
  obtain ⟨ε, δ, y, -, -, hxy, -, -⟩ := badLU_data hbad hx.1 hx.2
  exact ⟨y, mem_cfib_cons.mpr hxy⟩

lemma monoDom_of_badLD {Y : Set (Fin (k + 2) → ℝ)} {c : Fin k → ℝ} {u v : ℝ}
    (hbad : ∀ x : ℝ, u < x → x < v → Fin.cons x c ∈ BadLD Y) :
    Set.Ioo u v ⊆ MonoDom (Cfib Y c) := by
  intro x hx
  obtain ⟨ε, δ, y, -, -, hxy, -, -⟩ := badLD_data hbad hx.1 hx.2
  exact ⟨y, mem_cfib_cons.mpr hxy⟩

lemma notMonoW_of_badRU {Y : Set (Fin (k + 2) → ℝ)} {c : Fin k → ℝ} {u v : ℝ}
    (hfun : ∀ (c : Fin k → ℝ) (x y y' : ℝ), CGr Y c x y → CGr Y c x y' → y = y')
    (hbad : ∀ x : ℝ, u < x → x < v → Fin.cons x c ∈ BadRU Y) :
    ∀ x ∈ Set.Ioo u v, x ∉ MonoW (Cfib Y c) := by
  intro x hx hW
  obtain ⟨ε, δ, y, hε, hδ, hxy, hdom, hjm⟩ := badRU_data hbad hx.1 hx.2
  obtain ⟨y₀, η, hη, hxy₀, hcon⟩ := hW
  have hy : y = y₀ := hfun c x y y₀ hxy (mem_cfib_cons.mp hxy₀)
  have hz1 : x < x + min δ η / 2 := by linarith [lt_min hδ hη]
  have hz2 : x + min δ η / 2 < x + min δ η := by linarith [lt_min hδ hη]
  have hzmem : ![x + min δ η / 2, y₀] ∈ Cfib Y c :=
    hcon _ (by linarith [hη, lt_min hδ hη]) (by linarith [min_le_right δ η])
  have hz : CGr Y c (x + min δ η / 2) y₀ := mem_cfib_cons.mp hzmem
  have := hjm _ hz1 (by linarith [min_le_left δ η]) y₀ hz
  rw [hy] at this
  linarith

lemma notMonoW_of_badRD {Y : Set (Fin (k + 2) → ℝ)} {c : Fin k → ℝ} {u v : ℝ}
    (hfun : ∀ (c : Fin k → ℝ) (x y y' : ℝ), CGr Y c x y → CGr Y c x y' → y = y')
    (hbad : ∀ x : ℝ, u < x → x < v → Fin.cons x c ∈ BadRD Y) :
    ∀ x ∈ Set.Ioo u v, x ∉ MonoW (Cfib Y c) := by
  intro x hx hW
  obtain ⟨ε, δ, y, hε, hδ, hxy, hdom, hjm⟩ := badRD_data hbad hx.1 hx.2
  obtain ⟨y₀, η, hη, hxy₀, hcon⟩ := hW
  have hy : y = y₀ := hfun c x y y₀ hxy (mem_cfib_cons.mp hxy₀)
  have hz1 : x < x + min δ η / 2 := by linarith [lt_min hδ hη]
  have hz2 : x + min δ η / 2 < x + min δ η := by linarith [lt_min hδ hη]
  have hzmem : ![x + min δ η / 2, y₀] ∈ Cfib Y c :=
    hcon _ (by linarith [hη, lt_min hδ hη]) (by linarith [min_le_right δ η])
  have hz : CGr Y c (x + min δ η / 2) y₀ := mem_cfib_cons.mp hzmem
  have := hjm _ hz1 (by linarith [min_le_left δ η]) y₀ hz
  rw [hy] at this
  linarith

lemma notMonoW_of_badLU {Y : Set (Fin (k + 2) → ℝ)} {c : Fin k → ℝ} {u v : ℝ}
    (hfun : ∀ (c : Fin k → ℝ) (x y y' : ℝ), CGr Y c x y → CGr Y c x y' → y = y')
    (hbad : ∀ x : ℝ, u < x → x < v → Fin.cons x c ∈ BadLU Y) :
    ∀ x ∈ Set.Ioo u v, x ∉ MonoW (Cfib Y c) := by
  intro x hx hW
  obtain ⟨ε, δ, y, hε, hδ, hxy, hdom, hjm⟩ := badLU_data hbad hx.1 hx.2
  obtain ⟨y₀, η, hη, hxy₀, hcon⟩ := hW
  have hy : y = y₀ := hfun c x y y₀ hxy (mem_cfib_cons.mp hxy₀)
  have hz1 : x - min δ η < x := by linarith [lt_min hδ hη]
  have hz2 : x - min δ η + min δ η / 2 < x := by linarith [lt_min hδ hη]
  have hzmem : ![x - min δ η + min δ η / 2, y₀] ∈ Cfib Y c :=
    hcon _ (by linarith [min_le_right δ η, lt_min hδ hη]) (by linarith [lt_min hδ hη])
  have hz : CGr Y c (x - min δ η + min δ η / 2) y₀ := mem_cfib_cons.mp hzmem
  have := hjm _ (by linarith [min_le_left δ η, lt_min hδ hη]) hz2 y₀ hz
  rw [hy] at this
  linarith

lemma notMonoW_of_badLD {Y : Set (Fin (k + 2) → ℝ)} {c : Fin k → ℝ} {u v : ℝ}
    (hfun : ∀ (c : Fin k → ℝ) (x y y' : ℝ), CGr Y c x y → CGr Y c x y' → y = y')
    (hbad : ∀ x : ℝ, u < x → x < v → Fin.cons x c ∈ BadLD Y) :
    ∀ x ∈ Set.Ioo u v, x ∉ MonoW (Cfib Y c) := by
  intro x hx hW
  obtain ⟨ε, δ, y, hε, hδ, hxy, hdom, hjm⟩ := badLD_data hbad hx.1 hx.2
  obtain ⟨y₀, η, hη, hxy₀, hcon⟩ := hW
  have hy : y = y₀ := hfun c x y y₀ hxy (mem_cfib_cons.mp hxy₀)
  have hz1 : x - min δ η < x := by linarith [lt_min hδ hη]
  have hz2 : x - min δ η + min δ η / 2 < x := by linarith [lt_min hδ hη]
  have hzmem : ![x - min δ η + min δ η / 2, y₀] ∈ Cfib Y c :=
    hcon _ (by linarith [min_le_right δ η, lt_min hδ hη]) (by linarith [lt_min hδ hη])
  have hz : CGr Y c (x - min δ η + min δ η / 2) y₀ := mem_cfib_cons.mp hzmem
  have := hjm _ (by linarith [min_le_left δ η, lt_min hδ hη]) hz2 y₀ hz
  rw [hy] at this
  linarith

/-! ## Bad implies a one-sided germ type on the interval -/

lemma monoHp_of_badRU {Y : Set (Fin (k + 2) → ℝ)} {c : Fin k → ℝ} {u v : ℝ}
    (hbad : ∀ x : ℝ, u < x → x < v → Fin.cons x c ∈ BadRU Y) :
    Set.Ioo u v ⊆ MonoHp (Cfib Y c) := by
  intro x hx
  obtain ⟨ε, δ, y, hε, hδ, hxy, hdom, hjm⟩ := badRU_data hbad hx.1 hx.2
  rw [mem_MonoHp]
  refine ⟨min δ (v - x), y, lt_min hδ (by linarith [hx.2]), mem_cfib_cons.mpr hxy, ?_⟩
  intro z hz1 hz2
  have hzt : z < x + δ := by linarith [min_le_left δ (v - x)]
  obtain ⟨w, hw⟩ := hdom z (by linarith) hzt
  exact ⟨w, mem_cfib_cons.mpr hw, by have := hjm z hz1 hzt w hw; linarith⟩

lemma monoLp_of_badRD {Y : Set (Fin (k + 2) → ℝ)} {c : Fin k → ℝ} {u v : ℝ}
    (hbad : ∀ x : ℝ, u < x → x < v → Fin.cons x c ∈ BadRD Y) :
    Set.Ioo u v ⊆ MonoLp (Cfib Y c) := by
  intro x hx
  obtain ⟨ε, δ, y, hε, hδ, hxy, hdom, hjm⟩ := badRD_data hbad hx.1 hx.2
  rw [mem_MonoLp]
  refine ⟨min δ (v - x), y, lt_min hδ (by linarith [hx.2]), mem_cfib_cons.mpr hxy, ?_⟩
  intro z hz1 hz2
  have hzt : z < x + δ := by linarith [min_le_left δ (v - x)]
  obtain ⟨w, hw⟩ := hdom z (by linarith) hzt
  exact ⟨w, mem_cfib_cons.mpr hw, by have := hjm z hz1 hzt w hw; linarith⟩

lemma monoHm_of_badLU {Y : Set (Fin (k + 2) → ℝ)} {c : Fin k → ℝ} {u v : ℝ}
    (hbad : ∀ x : ℝ, u < x → x < v → Fin.cons x c ∈ BadLU Y) :
    Set.Ioo u v ⊆ MonoHm (Cfib Y c) := by
  intro x hx
  obtain ⟨ε, δ, y, hε, hδ, hxy, hdom, hjm⟩ := badLU_data hbad hx.1 hx.2
  rw [mem_MonoHm]
  refine ⟨min δ (x - u), y, lt_min hδ (by linarith [hx.1]), mem_cfib_cons.mpr hxy, ?_⟩
  intro z hz1 hz2
  have hzt : x - δ < z := by linarith [min_le_left δ (x - u)]
  obtain ⟨w, hw⟩ := hdom z hzt (by linarith)
  exact ⟨w, mem_cfib_cons.mpr hw, by have := hjm z hzt hz2 w hw; linarith⟩

lemma monoLm_of_badLD {Y : Set (Fin (k + 2) → ℝ)} {c : Fin k → ℝ} {u v : ℝ}
    (hbad : ∀ x : ℝ, u < x → x < v → Fin.cons x c ∈ BadLD Y) :
    Set.Ioo u v ⊆ MonoLm (Cfib Y c) := by
  intro x hx
  obtain ⟨ε, δ, y, hε, hδ, hxy, hdom, hjm⟩ := badLD_data hbad hx.1 hx.2
  rw [mem_MonoLm]
  refine ⟨min δ (x - u), y, lt_min hδ (by linarith [hx.1]), mem_cfib_cons.mpr hxy, ?_⟩
  intro z hz1 hz2
  have hzt : x - δ < z := by linarith [min_le_left δ (x - u)]
  obtain ⟨w, hw⟩ := hdom z hzt (by linarith)
  exact ⟨w, mem_cfib_cons.mpr hw, by have := hjm z hzt hz2 w hw; linarith⟩

/-! ## Germ splitting on the interval -/

lemma germ_split_left {Y : Set (Fin (k + 2) → ℝ)} {c : Fin k → ℝ} {u v : ℝ} (huv : u < v)
    (hfun' : ∀ x y y' : ℝ, ![x, y] ∈ Cfib Y c → ![x, y'] ∈ Cfib Y c → y = y')
    (hDom : Set.Ioo u v ⊆ MonoDom (Cfib Y c))
    (hW : ∀ x ∈ Set.Ioo u v, x ∉ MonoW (Cfib Y c))
    (hLset : ∀ a : ℝ, ∃ s : Finset (Set ℝ), (∀ I ∈ s, I.OrdConnected) ∧
      MonoLset (Cfib Y c) a = ⋃₀ (s : Set (Set ℝ)))
    (hHset : ∀ a : ℝ, ∃ s : Finset (Set ℝ), (∀ I ∈ s, I.OrdConnected) ∧
      MonoHset (Cfib Y c) a = ⋃₀ (s : Set (Set ℝ)))
    (hLm_oc : ∃ s : Finset (Set ℝ), (∀ I ∈ s, I.OrdConnected) ∧
        {x : ℝ | Fin.cons x c ∈ PMonoLm Y} = ⋃₀ (s : Set (Set ℝ)))
    (hHm_oc : ∃ s : Finset (Set ℝ), (∀ I ∈ s, I.OrdConnected) ∧
        {x : ℝ | Fin.cons x c ∈ PMonoHm Y} = ⋃₀ (s : Set (Set ℝ))) :
    ∃ a b : ℝ, u ≤ a ∧ a < b ∧ b ≤ v ∧
      ((Set.Ioo a b ⊆ MonoLm (Cfib Y c)) ∨ (Set.Ioo a b ⊆ MonoHm (Cfib Y c))) := by
  obtain ⟨s₁, h₁, h₁'⟩ := hLm_oc
  obtain ⟨s₂, h₂, h₂'⟩ := hHm_oc
  have hsub : Set.Ioo u v ⊆ ⋃₀ (((s₁ ∪ s₂ : Finset (Set ℝ))) : Set (Set ℝ)) := by
    intro x hx
    rcases (germ_cover hfun' (fun S hS y => finUnionOrd_germ hS y) hLset hHset hDom hW hx).1
      with h | h
    · have hx1 : x ∈ ⋃₀ ((s₁ : Finset (Set ℝ)) : Set (Set ℝ)) := by rw [← h₁']; exact h
      obtain ⟨I, hI, hxI⟩ := Set.mem_sUnion.mp hx1
      exact Set.mem_sUnion.mpr ⟨I, Finset.mem_coe.mpr
        (Finset.mem_union_left _ (Finset.mem_coe.mp hI)), hxI⟩
    · have hx2 : x ∈ ⋃₀ ((s₂ : Finset (Set ℝ)) : Set (Set ℝ)) := by rw [← h₂']; exact h
      obtain ⟨I, hI, hxI⟩ := Set.mem_sUnion.mp hx2
      exact Set.mem_sUnion.mpr ⟨I, Finset.mem_coe.mpr
        (Finset.mem_union_right _ (Finset.mem_coe.mp hI)), hxI⟩
  have hord : ∀ I ∈ (s₁ ∪ s₂ : Finset (Set ℝ)), I.OrdConnected := by
    intro I hI
    rcases Finset.mem_union.mp hI with h | h
    · exact h₁ I h
    · exact h₂ I h
  obtain ⟨I, hI, a, b, hua, hab, hbv, hIab⟩ := ordConnected_cover_subinterval hord huv hsub
  rcases Finset.mem_union.mp hI with h | h
  · refine ⟨a, b, hua, hab, hbv, Or.inl ?_⟩
    intro x hx
    have h1 : x ∈ ⋃₀ ((s₁ : Finset (Set ℝ)) : Set (Set ℝ)) :=
      Set.subset_sUnion_of_mem (Finset.mem_coe.mpr h) (hIab hx)
    have h2 : Fin.cons x c ∈ PMonoLm Y := by rw [← h₁'] at h1; exact h1
    simpa using h2
  · refine ⟨a, b, hua, hab, hbv, Or.inr ?_⟩
    intro x hx
    have h1 : x ∈ ⋃₀ ((s₂ : Finset (Set ℝ)) : Set (Set ℝ)) :=
      Set.subset_sUnion_of_mem (Finset.mem_coe.mpr h) (hIab hx)
    have h2 : Fin.cons x c ∈ PMonoHm Y := by rw [← h₂'] at h1; exact h1
    simpa using h2

lemma germ_split_right {Y : Set (Fin (k + 2) → ℝ)} {c : Fin k → ℝ} {u v : ℝ} (huv : u < v)
    (hfun' : ∀ x y y' : ℝ, ![x, y] ∈ Cfib Y c → ![x, y'] ∈ Cfib Y c → y = y')
    (hDom : Set.Ioo u v ⊆ MonoDom (Cfib Y c))
    (hW : ∀ x ∈ Set.Ioo u v, x ∉ MonoW (Cfib Y c))
    (hLset : ∀ a : ℝ, ∃ s : Finset (Set ℝ), (∀ I ∈ s, I.OrdConnected) ∧
      MonoLset (Cfib Y c) a = ⋃₀ (s : Set (Set ℝ)))
    (hHset : ∀ a : ℝ, ∃ s : Finset (Set ℝ), (∀ I ∈ s, I.OrdConnected) ∧
      MonoHset (Cfib Y c) a = ⋃₀ (s : Set (Set ℝ)))
    (hLp_oc : ∃ s : Finset (Set ℝ), (∀ I ∈ s, I.OrdConnected) ∧
        {x : ℝ | Fin.cons x c ∈ PMonoLp Y} = ⋃₀ (s : Set (Set ℝ)))
    (hHp_oc : ∃ s : Finset (Set ℝ), (∀ I ∈ s, I.OrdConnected) ∧
        {x : ℝ | Fin.cons x c ∈ PMonoHp Y} = ⋃₀ (s : Set (Set ℝ))) :
    ∃ a b : ℝ, u ≤ a ∧ a < b ∧ b ≤ v ∧
      ((Set.Ioo a b ⊆ MonoLp (Cfib Y c)) ∨ (Set.Ioo a b ⊆ MonoHp (Cfib Y c))) := by
  obtain ⟨s₁, h₁, h₁'⟩ := hLp_oc
  obtain ⟨s₂, h₂, h₂'⟩ := hHp_oc
  have hsub : Set.Ioo u v ⊆ ⋃₀ (((s₁ ∪ s₂ : Finset (Set ℝ))) : Set (Set ℝ)) := by
    intro x hx
    rcases (germ_cover hfun' (fun S hS y => finUnionOrd_germ hS y) hLset hHset hDom hW hx).2
      with h | h
    · have hx1 : x ∈ ⋃₀ ((s₁ : Finset (Set ℝ)) : Set (Set ℝ)) := by rw [← h₁']; exact h
      obtain ⟨I, hI, hxI⟩ := Set.mem_sUnion.mp hx1
      exact Set.mem_sUnion.mpr ⟨I, Finset.mem_coe.mpr
        (Finset.mem_union_left _ (Finset.mem_coe.mp hI)), hxI⟩
    · have hx2 : x ∈ ⋃₀ ((s₂ : Finset (Set ℝ)) : Set (Set ℝ)) := by rw [← h₂']; exact h
      obtain ⟨I, hI, hxI⟩ := Set.mem_sUnion.mp hx2
      exact Set.mem_sUnion.mpr ⟨I, Finset.mem_coe.mpr
        (Finset.mem_union_right _ (Finset.mem_coe.mp hI)), hxI⟩
  have hord : ∀ I ∈ (s₁ ∪ s₂ : Finset (Set ℝ)), I.OrdConnected := by
    intro I hI
    rcases Finset.mem_union.mp hI with h | h
    · exact h₁ I h
    · exact h₂ I h
  obtain ⟨I, hI, a, b, hua, hab, hbv, hIab⟩ := ordConnected_cover_subinterval hord huv hsub
  rcases Finset.mem_union.mp hI with h | h
  · refine ⟨a, b, hua, hab, hbv, Or.inl ?_⟩
    intro x hx
    have h1 : x ∈ ⋃₀ ((s₁ : Finset (Set ℝ)) : Set (Set ℝ)) :=
      Set.subset_sUnion_of_mem (Finset.mem_coe.mpr h) (hIab hx)
    have h2 : Fin.cons x c ∈ PMonoLp Y := by rw [← h₁'] at h1; exact h1
    simpa using h2
  · refine ⟨a, b, hua, hab, hbv, Or.inr ?_⟩
    intro x hx
    have h1 : x ∈ ⋃₀ ((s₂ : Finset (Set ℝ)) : Set (Set ℝ)) :=
      Set.subset_sUnion_of_mem (Finset.mem_coe.mpr h) (hIab hx)
    have h2 : Fin.cons x c ∈ PMonoHp Y := by rw [← h₂'] at h1; exact h1
    simpa using h2

end Work.WilC4
