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
import Submission.Work.WilC4.cbAux
import Submission.Work.WilC4.critFibreOrd
import Submission.Work.WilC4.not_mono_rightJump

set_option autoImplicit false
set_option maxHeartbeats 1000000
noncomputable section
open Classical FirstOrder FirstOrder.Language
namespace Work.WilC4
open WilkiesDesign WilkiesDesign.CG

variable {k : ℕ}

/-! ## The extended fibre function -/

noncomputable def fibreFun (Y : Set (Fin (k + 2) → ℝ)) (c : Fin k → ℝ) : ℝ → ℝ :=
  fun x => if h : ∃ y : ℝ, CGr Y c x y then Classical.choose h else 0

lemma fibreFun_spec {Y : Set (Fin (k + 2) → ℝ)} {c : Fin k → ℝ} {x : ℝ}
    (h : ∃ y : ℝ, CGr Y c x y) : CGr Y c x (fibreFun Y c x) := by
  unfold fibreFun
  rw [dif_pos h]
  exact Classical.choose_spec h

/-! ## Bad implies a contradiction on a monotone interval -/

lemma badRU_false {Y : Set (Fin (k + 2) → ℝ)} {c : Fin k → ℝ} {a b : ℝ} (hab : a < b)
    (hfun : ∀ (c : Fin k → ℝ) (x y y' : ℝ), CGr Y c x y → CGr Y c x y' → y = y')
    (hdom : Set.Ioo a b ⊆ MonoDom (Cfib Y c))
    (hbad : ∀ x : ℝ, a < x → x < b → Fin.cons x c ∈ BadRU Y)
    (hmono : MonoIncOn (Cfib Y c) a b) : False := by
  have hCGr : ∀ x ∈ Set.Ioo a b, CGr Y c x (fibreFun Y c x) := fun x hx => by
    obtain ⟨y, hy⟩ := hdom hx
    exact fibreFun_spec ⟨y, hy⟩
  refine not_mono_rightJump (g := fibreFun Y c) hab ?_ ?_
  · intro x y hx1 hxy hy2
    exact ((mem_MonoIncOn (Y := Cfib Y c) (a := a) (b := b)).mp hmono) x y
      (fibreFun Y c x) (fibreFun Y c y) hx1 hxy hy2
      (mem_cfib_cons.mpr (hCGr x ⟨hx1, lt_trans hxy hy2⟩))
      (mem_cfib_cons.mpr (hCGr y ⟨lt_trans hx1 hxy, hy2⟩))
  · intro x hx1 hx2
    obtain ⟨ε, δ, y, hε, hδ, hxy, hdom', hjm⟩ := badRU_data hbad hx1 hx2
    refine ⟨ε, δ, hε, hδ, ?_⟩
    intro t ht1 ht2
    have hy : y = fibreFun Y c x := hfun c x y (fibreFun Y c x) hxy (hCGr x ⟨hx1, hx2⟩)
    have ht : ∃ w : ℝ, CGr Y c t w := hdom' t (by linarith) ht2
    have hle := hjm t ht1 ht2 (fibreFun Y c t) (fibreFun_spec ht)
    rw [hy] at hle
    exact hle

lemma badRD_false {Y : Set (Fin (k + 2) → ℝ)} {c : Fin k → ℝ} {a b : ℝ} (hab : a < b)
    (hfun : ∀ (c : Fin k → ℝ) (x y y' : ℝ), CGr Y c x y → CGr Y c x y' → y = y')
    (hdom : Set.Ioo a b ⊆ MonoDom (Cfib Y c))
    (hbad : ∀ x : ℝ, a < x → x < b → Fin.cons x c ∈ BadRD Y)
    (hmono : MonoDecOn (Cfib Y c) a b) : False := by
  have hCGr : ∀ x ∈ Set.Ioo a b, CGr Y c x (fibreFun Y c x) := fun x hx => by
    obtain ⟨y, hy⟩ := hdom hx
    exact fibreFun_spec ⟨y, hy⟩
  refine not_mono_rightJump (g := fun u : ℝ => -fibreFun Y c u) hab ?_ ?_
  · intro x y hx1 hxy hy2
    have h := ((mem_MonoDecOn (Y := Cfib Y c) (a := a) (b := b)).mp hmono) x y
      (fibreFun Y c x) (fibreFun Y c y) hx1 hxy hy2
      (mem_cfib_cons.mpr (hCGr x ⟨hx1, lt_trans hxy hy2⟩))
      (mem_cfib_cons.mpr (hCGr y ⟨lt_trans hx1 hxy, hy2⟩))
    linarith
  · intro x hx1 hx2
    obtain ⟨ε, δ, y, hε, hδ, hxy, hdom', hjm⟩ := badRD_data hbad hx1 hx2
    refine ⟨ε, δ, hε, hδ, ?_⟩
    intro t ht1 ht2
    have hy : y = fibreFun Y c x := hfun c x y (fibreFun Y c x) hxy (hCGr x ⟨hx1, hx2⟩)
    have ht : ∃ w : ℝ, CGr Y c t w := hdom' t (by linarith) ht2
    have hle := hjm t ht1 ht2 (fibreFun Y c t) (fibreFun_spec ht)
    rw [hy] at hle
    linarith

lemma badLU_false {Y : Set (Fin (k + 2) → ℝ)} {c : Fin k → ℝ} {a b : ℝ} (hab : a < b)
    (hfun : ∀ (c : Fin k → ℝ) (x y y' : ℝ), CGr Y c x y → CGr Y c x y' → y = y')
    (hdom : Set.Ioo a b ⊆ MonoDom (Cfib Y c))
    (hbad : ∀ x : ℝ, a < x → x < b → Fin.cons x c ∈ BadLU Y)
    (hmono : MonoDecOn (Cfib Y c) a b) : False := by
  have hCGr : ∀ x ∈ Set.Ioo a b, CGr Y c x (fibreFun Y c x) := fun x hx => by
    obtain ⟨y, hy⟩ := hdom hx
    exact fibreFun_spec ⟨y, hy⟩
  refine not_mono_rightJump (g := fun u : ℝ => fibreFun Y c (-u)) (a := -b) (b := -a)
    (by linarith) ?_ ?_
  · intro u v hu1 huv hv2
    have h1 : a < -v := by linarith
    have h2 : -v < -u := by linarith
    have h3 : -u < b := by linarith
    have h := ((mem_MonoDecOn (Y := Cfib Y c) (a := a) (b := b)).mp hmono) (-v) (-u)
      (fibreFun Y c (-v)) (fibreFun Y c (-u)) h1 h2 h3
      (mem_cfib_cons.mpr (hCGr (-v) ⟨h1, lt_trans h2 h3⟩))
      (mem_cfib_cons.mpr (hCGr (-u) ⟨lt_trans h1 h2, h3⟩))
    exact h
  · intro u hu1 hu2
    have hx1 : a < -u := by linarith
    have hx2 : -u < b := by linarith
    obtain ⟨ε, δ, y, hε, hδ, hxy, hdom', hjm⟩ := badLU_data hbad hx1 hx2
    refine ⟨ε, δ, hε, hδ, ?_⟩
    intro s hs1 hs2
    have hs1' : -u - δ < -s := by linarith
    have hs2' : -s < -u := by linarith
    have hy : y = fibreFun Y c (-u) :=
      hfun c (-u) y (fibreFun Y c (-u)) hxy (hCGr (-u) ⟨hx1, hx2⟩)
    have ht : ∃ w : ℝ, CGr Y c (-s) w := hdom' (-s) hs1' (by linarith)
    have hle := hjm (-s) hs1' hs2' (fibreFun Y c (-s)) (fibreFun_spec ht)
    rw [hy] at hle
    exact hle

lemma badLD_false {Y : Set (Fin (k + 2) → ℝ)} {c : Fin k → ℝ} {a b : ℝ} (hab : a < b)
    (hfun : ∀ (c : Fin k → ℝ) (x y y' : ℝ), CGr Y c x y → CGr Y c x y' → y = y')
    (hdom : Set.Ioo a b ⊆ MonoDom (Cfib Y c))
    (hbad : ∀ x : ℝ, a < x → x < b → Fin.cons x c ∈ BadLD Y)
    (hmono : MonoIncOn (Cfib Y c) a b) : False := by
  have hCGr : ∀ x ∈ Set.Ioo a b, CGr Y c x (fibreFun Y c x) := fun x hx => by
    obtain ⟨y, hy⟩ := hdom hx
    exact fibreFun_spec ⟨y, hy⟩
  refine not_mono_rightJump (g := fun u : ℝ => -fibreFun Y c (-u)) (a := -b) (b := -a)
    (by linarith) ?_ ?_
  · intro u v hu1 huv hv2
    have h1 : a < -v := by linarith
    have h2 : -v < -u := by linarith
    have h3 : -u < b := by linarith
    have h := ((mem_MonoIncOn (Y := Cfib Y c) (a := a) (b := b)).mp hmono) (-v) (-u)
      (fibreFun Y c (-v)) (fibreFun Y c (-u)) h1 h2 h3
      (mem_cfib_cons.mpr (hCGr (-v) ⟨h1, lt_trans h2 h3⟩))
      (mem_cfib_cons.mpr (hCGr (-u) ⟨lt_trans h1 h2, h3⟩))
    linarith
  · intro u hu1 hu2
    have hx1 : a < -u := by linarith
    have hx2 : -u < b := by linarith
    obtain ⟨ε, δ, y, hε, hδ, hxy, hdom', hjm⟩ := badLD_data hbad hx1 hx2
    refine ⟨ε, δ, hε, hδ, ?_⟩
    intro s hs1 hs2
    have hs1' : -u - δ < -s := by linarith
    have hs2' : -s < -u := by linarith
    have hy : y = fibreFun Y c (-u) :=
      hfun c (-u) y (fibreFun Y c (-u)) hxy (hCGr (-u) ⟨hx1, hx2⟩)
    have ht : ∃ w : ℝ, CGr Y c (-s) w := hdom' (-s) hs1' (by linarith)
    have hle := hjm (-s) hs1' hs2' (fibreFun Y c (-s)) (fibreFun_spec ht)
    rw [hy] at hle
    linarith

/-! ## The four cases -/

lemma badRU_noInterval (hOM : WilkiesDesign.CG.OMinModels)
    (Y : Set (Fin (k + 2) → ℝ))
    (hfun : ∀ (c : Fin k → ℝ) (x y y' : ℝ), CGr Y c x y → CGr Y c x y' → y = y')
    (hLset : ∀ (c : Fin k → ℝ) (a : ℝ), ∃ s : Finset (Set ℝ), (∀ I ∈ s, I.OrdConnected) ∧
      MonoLset (Cfib Y c) a = ⋃₀ (s : Set (Set ℝ)))
    (hHset : ∀ (c : Fin k → ℝ) (a : ℝ), ∃ s : Finset (Set ℝ), (∀ I ∈ s, I.OrdConnected) ∧
      MonoHset (Cfib Y c) a = ⋃₀ (s : Set (Set ℝ)))
    (hLm : (∅ : Set ℝ).Definable WilkiesDesign.CG.LRc (PMonoLm Y))
    (hHm : (∅ : Set ℝ).Definable WilkiesDesign.CG.LRc (PMonoHm Y))
    (hLp : (∅ : Set ℝ).Definable WilkiesDesign.CG.LRc (PMonoLp Y))
    (hHp : (∅ : Set ℝ).Definable WilkiesDesign.CG.LRc (PMonoHp Y))
    (c : Fin k → ℝ) {u v : ℝ} (huv : u < v)
    (hbad : ∀ x : ℝ, u < x → x < v → Fin.cons x c ∈ BadRU Y) : False := by
  have hfun' := cfib_fun (Y := Y) (c := c) hfun
  obtain ⟨hLm_oc, hHm_oc, hLp_oc, hHp_oc⟩ := critFibreOrd hOM Y hLm hHm hLp hHp c
  obtain ⟨a, b, hua, hab, hbv, hsplit⟩ := germ_split_left (Y := Y) (c := c) huv hfun'
    (monoDom_of_badRU hbad) (notMonoW_of_badRU hfun hbad) (hLset c) (hHset c) hLm_oc hHm_oc
  have hHpI : Set.Ioo a b ⊆ MonoHp (Cfib Y c) := fun x hx =>
    (monoHp_of_badRU hbad) ⟨lt_of_le_of_lt hua hx.1, lt_of_lt_of_le hx.2 hbv⟩
  rcases hsplit with hLmI | hHmI
  · exact badRU_false hab hfun
      (fun x hx => (monoDom_of_badRU hbad) ⟨lt_of_le_of_lt hua hx.1, lt_of_lt_of_le hx.2 hbv⟩)
      (fun x hx1 hx2 => hbad x (lt_of_le_of_lt hua hx1) (lt_of_lt_of_le hx2 hbv))
      ((germ_mono_of_types hfun').1 ⟨hLmI, hHpI⟩)
  · exact (germ_extr hab hfun').2 ⟨hHmI, hHpI⟩

lemma badRD_noInterval (hOM : WilkiesDesign.CG.OMinModels)
    (Y : Set (Fin (k + 2) → ℝ))
    (hfun : ∀ (c : Fin k → ℝ) (x y y' : ℝ), CGr Y c x y → CGr Y c x y' → y = y')
    (hLset : ∀ (c : Fin k → ℝ) (a : ℝ), ∃ s : Finset (Set ℝ), (∀ I ∈ s, I.OrdConnected) ∧
      MonoLset (Cfib Y c) a = ⋃₀ (s : Set (Set ℝ)))
    (hHset : ∀ (c : Fin k → ℝ) (a : ℝ), ∃ s : Finset (Set ℝ), (∀ I ∈ s, I.OrdConnected) ∧
      MonoHset (Cfib Y c) a = ⋃₀ (s : Set (Set ℝ)))
    (hLm : (∅ : Set ℝ).Definable WilkiesDesign.CG.LRc (PMonoLm Y))
    (hHm : (∅ : Set ℝ).Definable WilkiesDesign.CG.LRc (PMonoHm Y))
    (hLp : (∅ : Set ℝ).Definable WilkiesDesign.CG.LRc (PMonoLp Y))
    (hHp : (∅ : Set ℝ).Definable WilkiesDesign.CG.LRc (PMonoHp Y))
    (c : Fin k → ℝ) {u v : ℝ} (huv : u < v)
    (hbad : ∀ x : ℝ, u < x → x < v → Fin.cons x c ∈ BadRD Y) : False := by
  have hfun' := cfib_fun (Y := Y) (c := c) hfun
  obtain ⟨hLm_oc, hHm_oc, hLp_oc, hHp_oc⟩ := critFibreOrd hOM Y hLm hHm hLp hHp c
  obtain ⟨a, b, hua, hab, hbv, hsplit⟩ := germ_split_left (Y := Y) (c := c) huv hfun'
    (monoDom_of_badRD hbad) (notMonoW_of_badRD hfun hbad) (hLset c) (hHset c) hLm_oc hHm_oc
  have hLpI : Set.Ioo a b ⊆ MonoLp (Cfib Y c) := fun x hx =>
    (monoLp_of_badRD hbad) ⟨lt_of_le_of_lt hua hx.1, lt_of_lt_of_le hx.2 hbv⟩
  rcases hsplit with hLmI | hHmI
  · exact (germ_extr hab hfun').1 ⟨hLmI, hLpI⟩
  · exact badRD_false hab hfun
      (fun x hx => (monoDom_of_badRD hbad) ⟨lt_of_le_of_lt hua hx.1, lt_of_lt_of_le hx.2 hbv⟩)
      (fun x hx1 hx2 => hbad x (lt_of_le_of_lt hua hx1) (lt_of_lt_of_le hx2 hbv))
      ((germ_mono_of_types hfun').2 ⟨hHmI, hLpI⟩)

lemma badLU_noInterval (hOM : WilkiesDesign.CG.OMinModels)
    (Y : Set (Fin (k + 2) → ℝ))
    (hfun : ∀ (c : Fin k → ℝ) (x y y' : ℝ), CGr Y c x y → CGr Y c x y' → y = y')
    (hLset : ∀ (c : Fin k → ℝ) (a : ℝ), ∃ s : Finset (Set ℝ), (∀ I ∈ s, I.OrdConnected) ∧
      MonoLset (Cfib Y c) a = ⋃₀ (s : Set (Set ℝ)))
    (hHset : ∀ (c : Fin k → ℝ) (a : ℝ), ∃ s : Finset (Set ℝ), (∀ I ∈ s, I.OrdConnected) ∧
      MonoHset (Cfib Y c) a = ⋃₀ (s : Set (Set ℝ)))
    (hLm : (∅ : Set ℝ).Definable WilkiesDesign.CG.LRc (PMonoLm Y))
    (hHm : (∅ : Set ℝ).Definable WilkiesDesign.CG.LRc (PMonoHm Y))
    (hLp : (∅ : Set ℝ).Definable WilkiesDesign.CG.LRc (PMonoLp Y))
    (hHp : (∅ : Set ℝ).Definable WilkiesDesign.CG.LRc (PMonoHp Y))
    (c : Fin k → ℝ) {u v : ℝ} (huv : u < v)
    (hbad : ∀ x : ℝ, u < x → x < v → Fin.cons x c ∈ BadLU Y) : False := by
  have hfun' := cfib_fun (Y := Y) (c := c) hfun
  obtain ⟨hLm_oc, hHm_oc, hLp_oc, hHp_oc⟩ := critFibreOrd hOM Y hLm hHm hLp hHp c
  obtain ⟨a, b, hua, hab, hbv, hsplit⟩ := germ_split_right (Y := Y) (c := c) huv hfun'
    (monoDom_of_badLU hbad) (notMonoW_of_badLU hfun hbad) (hLset c) (hHset c) hLp_oc hHp_oc
  have hHmI : Set.Ioo a b ⊆ MonoHm (Cfib Y c) := fun x hx =>
    (monoHm_of_badLU hbad) ⟨lt_of_le_of_lt hua hx.1, lt_of_lt_of_le hx.2 hbv⟩
  rcases hsplit with hLpI | hHpI
  · exact badLU_false hab hfun
      (fun x hx => (monoDom_of_badLU hbad) ⟨lt_of_le_of_lt hua hx.1, lt_of_lt_of_le hx.2 hbv⟩)
      (fun x hx1 hx2 => hbad x (lt_of_le_of_lt hua hx1) (lt_of_lt_of_le hx2 hbv))
      ((germ_mono_of_types hfun').2 ⟨hHmI, hLpI⟩)
  · exact (germ_extr hab hfun').2 ⟨hHmI, hHpI⟩

lemma badLD_noInterval (hOM : WilkiesDesign.CG.OMinModels)
    (Y : Set (Fin (k + 2) → ℝ))
    (hfun : ∀ (c : Fin k → ℝ) (x y y' : ℝ), CGr Y c x y → CGr Y c x y' → y = y')
    (hLset : ∀ (c : Fin k → ℝ) (a : ℝ), ∃ s : Finset (Set ℝ), (∀ I ∈ s, I.OrdConnected) ∧
      MonoLset (Cfib Y c) a = ⋃₀ (s : Set (Set ℝ)))
    (hHset : ∀ (c : Fin k → ℝ) (a : ℝ), ∃ s : Finset (Set ℝ), (∀ I ∈ s, I.OrdConnected) ∧
      MonoHset (Cfib Y c) a = ⋃₀ (s : Set (Set ℝ)))
    (hLm : (∅ : Set ℝ).Definable WilkiesDesign.CG.LRc (PMonoLm Y))
    (hHm : (∅ : Set ℝ).Definable WilkiesDesign.CG.LRc (PMonoHm Y))
    (hLp : (∅ : Set ℝ).Definable WilkiesDesign.CG.LRc (PMonoLp Y))
    (hHp : (∅ : Set ℝ).Definable WilkiesDesign.CG.LRc (PMonoHp Y))
    (c : Fin k → ℝ) {u v : ℝ} (huv : u < v)
    (hbad : ∀ x : ℝ, u < x → x < v → Fin.cons x c ∈ BadLD Y) : False := by
  have hfun' := cfib_fun (Y := Y) (c := c) hfun
  obtain ⟨hLm_oc, hHm_oc, hLp_oc, hHp_oc⟩ := critFibreOrd hOM Y hLm hHm hLp hHp c
  obtain ⟨a, b, hua, hab, hbv, hsplit⟩ := germ_split_right (Y := Y) (c := c) huv hfun'
    (monoDom_of_badLD hbad) (notMonoW_of_badLD hfun hbad) (hLset c) (hHset c) hLp_oc hHp_oc
  have hLmI : Set.Ioo a b ⊆ MonoLm (Cfib Y c) := fun x hx =>
    (monoLm_of_badLD hbad) ⟨lt_of_le_of_lt hua hx.1, lt_of_lt_of_le hx.2 hbv⟩
  rcases hsplit with hLpI | hHpI
  · exact (germ_extr hab hfun').1 ⟨hLmI, hLpI⟩
  · exact badLD_false hab hfun
      (fun x hx => (monoDom_of_badLD hbad) ⟨lt_of_le_of_lt hua hx.1, lt_of_lt_of_le hx.2 hbv⟩)
      (fun x hx1 hx2 => hbad x (lt_of_le_of_lt hua hx1) (lt_of_lt_of_le hx2 hbv))
      ((germ_mono_of_types hfun').1 ⟨hLmI, hHpI⟩)

/-! ## Main theorem -/

theorem crit_bad_noInterval {k : ℕ} (hOM : WilkiesDesign.CG.OMinModels)
    (Y : Set (Fin (k + 2) → ℝ)) (hY : (∅ : Set ℝ).Definable WilkiesDesign.CG.LRc Y)
    (hfun : ∀ (c : Fin k → ℝ) (x y y' : ℝ), CGr Y c x y → CGr Y c x y' → y = y')
    (hIm : ∃ N : ℕ, ∀ (a b : ℝ) (c : Fin k → ℝ), ¬ AltChain N (ImFib Y a b c))
    (hLset : ∀ (c : Fin k → ℝ) (a : ℝ), ∃ s : Finset (Set ℝ), (∀ I ∈ s, I.OrdConnected) ∧
      MonoLset (Cfib Y c) a = ⋃₀ (s : Set (Set ℝ)))
    (hHset : ∀ (c : Fin k → ℝ) (a : ℝ), ∃ s : Finset (Set ℝ), (∀ I ∈ s, I.OrdConnected) ∧
      MonoHset (Cfib Y c) a = ⋃₀ (s : Set (Set ℝ)))
    (hLm : (∅ : Set ℝ).Definable WilkiesDesign.CG.LRc (PMonoLm Y))
    (hHm : (∅ : Set ℝ).Definable WilkiesDesign.CG.LRc (PMonoHm Y))
    (hLp : (∅ : Set ℝ).Definable WilkiesDesign.CG.LRc (PMonoLp Y))
    (hHp : (∅ : Set ℝ).Definable WilkiesDesign.CG.LRc (PMonoHp Y))
    (c : Fin k → ℝ) :
    (∀ u v : ℝ, u < v → ¬ (∀ x : ℝ, u < x → x < v → Fin.cons x c ∈ BadRU Y)) ∧
    (∀ u v : ℝ, u < v → ¬ (∀ x : ℝ, u < x → x < v → Fin.cons x c ∈ BadRD Y)) ∧
    (∀ u v : ℝ, u < v → ¬ (∀ x : ℝ, u < x → x < v → Fin.cons x c ∈ BadLU Y)) ∧
    (∀ u v : ℝ, u < v → ¬ (∀ x : ℝ, u < x → x < v → Fin.cons x c ∈ BadLD Y)) := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro u v huv hbad
    exact badRU_noInterval hOM Y hfun hLset hHset hLm hHm hLp hHp c huv hbad
  · intro u v huv hbad
    exact badRD_noInterval hOM Y hfun hLset hHset hLm hHm hLp hHp c huv hbad
  · intro u v huv hbad
    exact badLU_noInterval hOM Y hfun hLset hHset hLm hHm hLp hHp c huv hbad
  · intro u v huv hbad
    exact badLD_noInterval hOM Y hfun hLset hHset hLm hHm hLp hHp c huv hbad

end Work.WilC4
