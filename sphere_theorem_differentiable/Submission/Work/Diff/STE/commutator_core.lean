import Mathlib
import Submission.Work.Diff.STE.Torus
import Submission.Work.Diff.STE.commutator_defs
import Submission.Work.Diff.STE.commutator_pd
import Submission.Work.Diff.STE.fourierCoeff_pd
import Submission.Work.Diff.STE.exists_bound_pdRList

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

/-!
# Elementary estimates for the commutator estimate

* `cm_splits_length_count`, `cm_splits_mem_length` : bookkeeping for `splits`;
* `cm_list_sum_norm_le` : `‖∑_{p ∈ L} f p‖ ≤ ∑_{p ∈ L} ‖f p‖` for `List.sum`;
* `cm_L2re_sum` : linearity of `L2re` in its first argument over a finite sum;
* `cm_term_bound` : the elementary `L²` bound `|∫ F g h̄| ≤ Mη∫‖g‖² + M/(4η)∫‖h‖²` for
  `‖F‖ ≤ M` (pointwise AM-GM; no Cauchy–Schwarz needed);
* `cm_integral_pdList_le_ENormSq` : `∫ ‖∂^q f‖² ≤ ENormSq |q| f`;
* `cm_ENormSq_le_pow` : iterating the Poincaré inequality.
-/

noncomputable section

namespace Work.Diff.STE

open MeasureTheory BigOperators

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

lemma cm_splits_length_count {α : Type*} (l : List α) : (splits l).length = 2 ^ l.length := by
  induction l with
  | nil => rfl
  | cons i l ih =>
      rw [splits, List.length_append, List.length_map, List.length_map, ih, List.length_cons,
        pow_succ]
      ring

lemma cm_splits_mem_length {α : Type*} : ∀ (l : List α) (p : List α × List α),
    p ∈ splits l → p.1.length + p.2.length = l.length := by
  intro l
  induction l with
  | nil =>
      intro p hp
      simp only [splits, List.mem_singleton] at hp
      subst hp
      simp
  | cons i l ih =>
      intro p hp
      rw [splits] at hp
      rcases List.mem_append.mp hp with h | h
      · obtain ⟨q, hq, hqp⟩ := List.mem_map.mp h
        rw [← hqp]
        have hlen := ih q hq
        simp only [List.length_cons]
        omega
      · obtain ⟨q, hq, hqp⟩ := List.mem_map.mp h
        rw [← hqp]
        have hlen := ih q hq
        simp only [List.length_cons]
        omega

/-- A continuous real function is integrable on the unit cube. -/
lemma cm_integrableOn_unitCube_of_continuous {F : (ι → ℝ) → ℝ} (hF : Continuous F) :
    Integrable F (volume.restrict unitCube) := by
  have hC : IsCompact (Set.pi Set.univ (fun _ : ι => Set.Icc (0 : ℝ) 1)) :=
    isCompact_univ_pi (fun _ => isCompact_Icc)
  have hsub : unitCube ⊆ Set.pi Set.univ (fun _ : ι => Set.Icc (0 : ℝ) 1) := by
    intro x hx
    simp only [unitCube, Set.mem_pi, Set.mem_univ, true_implies] at hx ⊢
    exact fun j => ⟨le_of_lt (hx j).1, (hx j).2⟩
  exact (ContinuousOn.integrableOn_compact hC hF.continuousOn).mono_set hsub

/-- Norm of a `List.sum` of vectors. -/
lemma cm_list_sum_norm_le {α : Type*} {E : Type*} [SeminormedAddCommGroup E] (L : List α)
    (f : α → E) :
    ‖(L.map f).sum‖ ≤ (L.map (fun a => ‖f a‖)).sum := by
  induction L with
  | nil => simp
  | cons a L ih =>
      simp only [List.map_cons, List.sum_cons]
      exact le_trans (norm_add_le _ _) (add_le_add le_rfl ih)

/-- Linearity of `L2re` in the first argument. -/
lemma cm_L2re_sum {β : Type*} (S : Finset β) (f : β → (ι → ℝ) → ℂ) (g : (ι → ℝ) → ℂ)
    (hf : ∀ b ∈ S, Continuous (f b)) (hg : Continuous g) :
    L2re (fun x => ∑ b ∈ S, f b x) g = ∑ b ∈ S, L2re (f b) g := by
  have hint : ∀ b ∈ S, Integrable (fun x => f b x * star (g x)) (volume.restrict unitCube) :=
    fun b hb => integrableOn_unitCube_of_continuous ((hf b hb).mul (continuous_star.comp hg))
  simp only [L2re]
  rw [show (fun x => (∑ b ∈ S, f b x) * star (g x))
        = fun x => ∑ b ∈ S, f b x * star (g x) by
      funext x; rw [Finset.sum_mul]]
  rw [integral_finset_sum S hint]
  simpa [Complex.reCLM_apply] using
    (map_sum Complex.reCLM (fun b => ∫ x in unitCube, f b x * star (g x)) S)

/-- The elementary bound `|∫ F g h̄| ≤ M η ∫‖g‖² + M/(4η) ∫‖h‖²` for `‖F‖ ≤ M`. -/
lemma cm_term_bound (M η : ℝ) (hM0 : 0 ≤ M) (hη : 0 < η) (F g h : (ι → ℝ) → ℂ)
    (hcF : Continuous F) (hcg : Continuous g) (hch : Continuous h)
    (hFb : ∀ x, ‖F x‖ ≤ M) :
    |L2re (fun x => F x * g x) h|
      ≤ M * η * (∫ x in unitCube, ‖g x‖ ^ 2)
        + (M / (4 * η)) * (∫ x in unitCube, ‖h x‖ ^ 2) := by
  have hη4 : 0 < 4 * η := by linarith
  have hInt : ∀ (a b : (ι → ℝ) → ℂ), Continuous a → Continuous b →
      Integrable (fun x => ‖a x‖ * ‖b x‖) (volume.restrict unitCube) :=
    fun a b ha hb => cm_integrableOn_unitCube_of_continuous (ha.norm.mul hb.norm)
  -- step 1: the absolute value of the real part is at most the integral of the norm
  have hstep1 : |L2re (fun x => F x * g x) h|
      ≤ ∫ x in unitCube, ‖F x‖ * ‖g x‖ * ‖h x‖ := by
    simp only [L2re]
    have h1 : |(∫ x in unitCube, F x * g x * star (h x)).re|
        ≤ ‖∫ x in unitCube, F x * g x * star (h x)‖ := Complex.abs_re_le_norm _
    have h2 : ‖∫ x in unitCube, F x * g x * star (h x)‖
        ≤ ∫ x in unitCube, ‖F x * g x * star (h x)‖ := norm_integral_le_integral_norm _
    refine le_trans h1 (le_trans h2 (le_of_eq ?_))
    refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
    simp only [norm_mul, norm_star, mul_assoc]
  -- step 2: pull out the bound `M`
  have hstep2 : ∫ x in unitCube, ‖F x‖ * ‖g x‖ * ‖h x‖
      ≤ M * ∫ x in unitCube, ‖g x‖ * ‖h x‖ := by
    have hint1 : Integrable (fun x => ‖F x‖ * ‖g x‖ * ‖h x‖) (volume.restrict unitCube) :=
      cm_integrableOn_unitCube_of_continuous ((hcF.norm.mul hcg.norm).mul hch.norm)
    have hint2 : Integrable (fun x => ‖g x‖ * ‖h x‖) (volume.restrict unitCube) :=
      hInt g h hcg hch
    rw [← integral_const_mul M (fun x => ‖g x‖ * ‖h x‖)]
    refine integral_mono hint1 (hint2.const_mul M) (fun x => ?_)
    calc ‖F x‖ * ‖g x‖ * ‖h x‖ ≤ M * ‖g x‖ * ‖h x‖ :=
          mul_le_mul_of_nonneg_right
            (mul_le_mul_of_nonneg_right (hFb x) (norm_nonneg _)) (norm_nonneg _)
      _ = M * (‖g x‖ * ‖h x‖) := by ring
  -- step 3: the pointwise AM-GM
  have hpt : ∀ x : ι → ℝ, ‖g x‖ * ‖h x‖
      ≤ η * ‖g x‖ ^ 2 + (1 / (4 * η)) * ‖h x‖ ^ 2 := by
    intro x
    have hA : (0 : ℝ) ≤ ‖g x‖ := norm_nonneg _
    have hB : (0 : ℝ) ≤ ‖h x‖ := norm_nonneg _
    have hsq : 0 ≤ (2 * η * ‖g x‖ - ‖h x‖) ^ 2 := sq_nonneg _
    have hkey : 4 * η * (1 / (4 * η)) = 1 := by field_simp
    nlinarith [hsq, hkey]
  have hstep3 : M * ∫ x in unitCube, ‖g x‖ * ‖h x‖
      ≤ M * (η * (∫ x in unitCube, ‖g x‖ ^ 2)
        + (1 / (4 * η)) * (∫ x in unitCube, ‖h x‖ ^ 2)) := by
    refine mul_le_mul_of_nonneg_left ?_ hM0
    have hint1 : Integrable (fun x => ‖g x‖ * ‖h x‖) (volume.restrict unitCube) := hInt g h hcg hch
    have hint2 : Integrable (fun x => η * ‖g x‖ ^ 2 + (1 / (4 * η)) * ‖h x‖ ^ 2)
        (volume.restrict unitCube) :=
      (cm_integrableOn_unitCube_of_continuous (hcg.norm.pow 2)).const_mul η |>.add
        ((cm_integrableOn_unitCube_of_continuous (hch.norm.pow 2)).const_mul (1 / (4 * η)))
    calc ∫ x in unitCube, ‖g x‖ * ‖h x‖
        ≤ ∫ x in unitCube, (η * ‖g x‖ ^ 2 + (1 / (4 * η)) * ‖h x‖ ^ 2) :=
          integral_mono hint1 hint2 hpt
      _ = η * (∫ x in unitCube, ‖g x‖ ^ 2)
            + (1 / (4 * η)) * (∫ x in unitCube, ‖h x‖ ^ 2) := by
          rw [integral_add]
          · rw [integral_const_mul, integral_const_mul]
          · exact (cm_integrableOn_unitCube_of_continuous (hcg.norm.pow 2)).const_mul η
          · exact (cm_integrableOn_unitCube_of_continuous (hch.norm.pow 2)).const_mul (1 / (4 * η))
  calc |L2re (fun x => F x * g x) h|
      ≤ ∫ x in unitCube, ‖F x‖ * ‖g x‖ * ‖h x‖ := hstep1
    _ ≤ M * ∫ x in unitCube, ‖g x‖ * ‖h x‖ := hstep2
    _ ≤ M * (η * (∫ x in unitCube, ‖g x‖ ^ 2)
          + (1 / (4 * η)) * (∫ x in unitCube, ‖h x‖ ^ 2)) := hstep3
    _ = M * η * (∫ x in unitCube, ‖g x‖ ^ 2)
          + (M / (4 * η)) * (∫ x in unitCube, ‖h x‖ ^ 2) := by ring

lemma cm_integral_pdList_le_ENormSq (q : List ι) (f : (ι → ℝ) → ℂ) :
    ∫ x in unitCube, ‖pdList q f x‖ ^ 2 ≤ ENormSq q.length f := by
  have hkey : pdVec q.length (q.get) f = pdList q f := by
    simp only [pdVec, List.ofFn_get]
  rw [← hkey]
  simp only [ENormSq]
  have h := Finset.single_le_sum (s := (Finset.univ : Finset (Fin q.length → ι)))
    (f := fun l => ∫ x in unitCube, ‖pdVec q.length l f x‖ ^ 2)
    (fun l _ => integral_nonneg fun x => by positivity) (Finset.mem_univ q.get)
  simpa using h

lemma cm_ENormSq_nonneg (m : ℕ) (f : (ι → ℝ) → ℂ) : 0 ≤ ENormSq m f := by
  simp only [ENormSq]
  exact Finset.sum_nonneg fun l _ => integral_nonneg fun x => by positivity

lemma cm_ENormSq_le_pow (CP : ℝ) (hCP0 : 0 ≤ CP) (M : ℕ) (f : (ι → ℝ) → ℂ)
    (hEN : ∀ j : ℕ, 1 ≤ j → j ≤ M → ENormSq j f ≤ CP * ENormSq (j + 1) f) :
    ∀ j m : ℕ, 1 ≤ j → j ≤ m → m ≤ M + 1 → ENormSq j f ≤ CP ^ (m - j) * ENormSq m f := by
  intro j m hj hjm hmM
  induction m with
  | zero => omega
  | succ m ih =>
      rcases Nat.eq_or_lt_of_le hjm with heq | hlt
      · subst heq
        simp
      · have hle : j ≤ m := by omega
        have hm1 : 1 ≤ m := le_trans hj hle
        have hmM' : m ≤ M := by omega
        have ihm : ENormSq j f ≤ CP ^ (m - j) * ENormSq m f := ih hle (by omega)
        have hEm : ENormSq m f ≤ CP * ENormSq (m + 1) f := hEN m hm1 hmM'
        have hEm0 : 0 ≤ ENormSq m f := cm_ENormSq_nonneg m f
        calc ENormSq j f ≤ CP ^ (m - j) * ENormSq m f := ihm
          _ ≤ CP ^ (m - j) * (CP * ENormSq (m + 1) f) := by
                refine mul_le_mul_of_nonneg_left hEm (by positivity)
          _ = CP ^ (m + 1 - j) * ENormSq (m + 1) f := by
                rw [show m + 1 - j = (m - j) + 1 by omega, pow_succ]
                ring


/-- Additivity of `L2re` in the first argument. -/
lemma cm_L2re_add (f g h : (ι → ℝ) → ℂ) (hf : Continuous f) (hg : Continuous g)
    (hh : Continuous h) : L2re (fun x => f x + g x) h = L2re f h + L2re g h := by
  have hint1 : Integrable (fun x => f x * star (h x)) (volume.restrict unitCube) :=
    integrableOn_unitCube_of_continuous (hf.mul (continuous_star.comp hh))
  have hint2 : Integrable (fun x => g x * star (h x)) (volume.restrict unitCube) :=
    integrableOn_unitCube_of_continuous (hg.mul (continuous_star.comp hh))
  simp only [L2re]
  rw [show (fun x => (f x + g x) * star (h x))
        = fun x => (f x * star (h x) + g x * star (h x)) by
      funext x; ring]
  rw [integral_add hint1 hint2]
  simpa [Complex.reCLM_apply] using
    (map_add Complex.reCLM (∫ x in unitCube, f x * star (h x))
      (∫ x in unitCube, g x * star (h x)))

/-- Continuity of a list sum of continuous functions. -/
lemma cm_continuous_list_sum {γ : Type*} (L : List γ) (f : γ → (ι → ℝ) → ℂ)
    (hf : ∀ p ∈ L, Continuous (f p)) : Continuous (fun x => (L.map f).sum x) := by
  induction L with
  | nil => simpa using continuous_const
  | cons a L ih =>
      have hf' : ∀ p ∈ L, Continuous (f p) := fun p hp => hf p (List.mem_cons_of_mem a hp)
      have hha : Continuous (f a) := hf a List.mem_cons_self
      simpa only [List.map_cons, List.sum_cons] using hha.add (ih hf')

/-- The pointwise sum of values of a list of functions is the value of their sum. -/
lemma cm_list_sum_apply {γ : Type*} : ∀ (L : List γ) (g : γ → (ι → ℝ) → ℂ),
    (fun x => (L.map (fun p => g p x)).sum) = (L.map g).sum := by
  intro L
  induction L with
  | nil => intro g; rfl
  | cons a L ih =>
      intro g
      have h2 : (fun x => (L.map (fun p => g p x)).sum) = (L.map g).sum := ih g
      funext x
      simp only [List.map_cons, List.sum_cons, Pi.add_apply]
      rw [congrFun h2 x]

/-- Linearity of `L2re` in the first argument along a list sum. -/
lemma cm_L2re_list_sum {γ : Type*} (L : List γ) (f : γ → (ι → ℝ) → ℂ) (h : (ι → ℝ) → ℂ)
    (hf : ∀ p ∈ L, Continuous (f p)) (hh : Continuous h) :
    L2re ((L.map f).sum) h = (L.map (fun p => L2re (f p) h)).sum := by
  induction L with
  | nil => simp [L2re]
  | cons a L ih =>
      have hf' : ∀ p ∈ L, Continuous (f p) := fun p hp => hf p (List.mem_cons_of_mem a hp)
      have hha : Continuous (f a) := hf a List.mem_cons_self
      have hhL : Continuous (fun x => (L.map f).sum x) := cm_continuous_list_sum L f hf'
      have ih' := ih hf'
      have hsplit : (f a + (L.map f).sum) = fun x => f a x + (L.map f).sum x := rfl
      simp only [List.map_cons, List.sum_cons]
      rw [hsplit, cm_L2re_add (f a) (fun x => (L.map f).sum x) h hha hhL hh, ih']

/-- `|∑| ≤ ∑|·|` for a list sum. -/
lemma cm_list_abs_sum_le {γ : Type*} (L : List γ) (f : γ → ℝ) :
    |(L.map f).sum| ≤ (L.map (fun a => |f a|)).sum := by
  simpa only [Real.norm_eq_abs] using cm_list_sum_norm_le L f

/-- **The commutator bound.**  Given the iterated Leibniz expansion of
`∂^L(F g) - F ∂^L g` (as the sum over the nonempty-left part of `splits L`), the `L²` pairing of
the commutator with `h` is bounded by the number of Leibniz terms times the elementary term
bound `M η G + M/(4η) H`. -/
lemma cm_comm_bound (M η G H : ℝ) (hM0 : 0 ≤ M) (hη : 0 < η) (hG0 : 0 ≤ G) (hH0 : 0 ≤ H)
    (L : List ι) (F g h : (ι → ℝ) → ℂ)
    (hleib : (fun y => pdList L (fun z => F z * g z) y - F y * pdList L g y)
        = fun y => (((splits L).filter (fun p => p.1 ≠ [])).map
            (fun p => pdList p.1 F y * pdList p.2 g y)).sum)
    (hcontF : ∀ q : List ι, q.length ≤ L.length → Continuous (pdList q F))
    (hcontg : ∀ q : List ι, q.length ≤ L.length → Continuous (pdList q g))
    (hconth : Continuous h)
    (hFb : ∀ q : List ι, q.length ≤ L.length → ∀ x, ‖pdList q F x‖ ≤ M)
    (hA : ∀ q : List ι, q.length < L.length → ∫ x in unitCube, ‖pdList q g x‖ ^ 2 ≤ G)
    (hAh : ∫ x in unitCube, ‖h x‖ ^ 2 ≤ H) :
    |L2re (fun x => pdList L (fun z => F z * g z) x - F x * pdList L g x) h|
      ≤ ((splits L).length : ℝ) * (M * η * G + (M / (4 * η)) * H) := by
  set Sf : List (List ι × List ι) := (splits L).filter (fun p => p.1 ≠ []) with hSf
  -- each Leibniz term satisfies the elementary bound
  have hterm : ∀ p ∈ Sf, |L2re (fun y => pdList p.1 F y * pdList p.2 g y) h|
      ≤ M * η * G + (M / (4 * η)) * H := by
    intro p hp
    obtain ⟨hp', hneBool⟩ := List.mem_filter.mp hp
    have hne : p.1 ≠ [] := of_decide_eq_true hneBool
    have hlen := cm_splits_mem_length L p hp'
    have hlen1 : p.1.length ≤ L.length := by omega
    have hlen2 : p.2.length < L.length := by
      have hpos : 0 < p.1.length := List.length_pos_of_ne_nil hne
      omega
    have hcont1 : Continuous (pdList p.1 F) := hcontF p.1 hlen1
    have hcont2 : Continuous (pdList p.2 g) := hcontg p.2 (le_of_lt hlen2)
    have hbd : ∀ x, ‖pdList p.1 F x‖ ≤ M := hFb p.1 hlen1
    have hIntg : ∫ x in unitCube, ‖pdList p.2 g x‖ ^ 2 ≤ G := hA p.2 hlen2
    have htb := cm_term_bound M η hM0 hη (pdList p.1 F) (pdList p.2 g) h hcont1 hcont2 hconth hbd
    have h1 : M * η * (∫ x in unitCube, ‖pdList p.2 g x‖ ^ 2) ≤ M * η * G :=
      mul_le_mul_of_nonneg_left hIntg (by positivity)
    have h2 : M / (4 * η) * (∫ x in unitCube, ‖h x‖ ^ 2) ≤ M / (4 * η) * H :=
      mul_le_mul_of_nonneg_left hAh (by positivity)
    linarith [htb, h1, h2]
  -- linearity plus the triangle inequality
  have hcontGf : ∀ p ∈ Sf, Continuous (fun y => pdList p.1 F y * pdList p.2 g y) := by
    intro p hp
    obtain ⟨hp', hneBool⟩ := List.mem_filter.mp hp
    have hlen := cm_splits_mem_length L p hp'
    exact (hcontF p.1 (by omega)).mul (hcontg p.2 (by omega))
  have hlin : L2re ((Sf.map (fun p => fun y => pdList p.1 F y * pdList p.2 g y)).sum) h
      = (Sf.map (fun p => L2re (fun y => pdList p.1 F y * pdList p.2 g y) h)).sum :=
    cm_L2re_list_sum Sf (fun p y => pdList p.1 F y * pdList p.2 g y) h hcontGf hconth
  have hsum : |(Sf.map (fun p => L2re (fun y => pdList p.1 F y * pdList p.2 g y) h)).sum|
      ≤ (Sf.map (fun p => M * η * G + (M / (4 * η)) * H)).sum := by
    calc |(Sf.map (fun p => L2re (fun y => pdList p.1 F y * pdList p.2 g y) h)).sum|
        ≤ (Sf.map (fun p => |L2re (fun y => pdList p.1 F y * pdList p.2 g y) h|)).sum :=
          cm_list_abs_sum_le Sf _
      _ ≤ (Sf.map (fun _ => M * η * G + (M / (4 * η)) * H)).sum :=
          List.sum_le_sum (fun p hp => hterm p hp)
  have hconst : (Sf.map (fun _ => M * η * G + (M / (4 * η)) * H)).sum
      = (Sf.length : ℝ) * (M * η * G + (M / (4 * η)) * H) := by
    induction Sf with
    | nil => simp
    | cons a L ih =>
        simp only [List.map_cons, List.sum_cons, List.length_cons] at ih ⊢
        rw [ih]
        push_cast
        ring
  have hlenSf : (Sf.length : ℝ) ≤ ((splits L).length : ℝ) := by
    have h : Sf.length ≤ (splits L).length := by
      rw [hSf]; exact List.length_filter_le _ (splits L)
    exact_mod_cast h
  have hB0 : 0 ≤ M * η * G + (M / (4 * η)) * H := by
    have h1 : 0 ≤ M * η * G := by positivity
    have h2 : 0 ≤ M / (4 * η) * H := by positivity
    linarith
  have hfun : (fun y => (List.map (fun p => pdList p.1 F y * pdList p.2 g y) Sf).sum)
      = (Sf.map (fun p => fun y => pdList p.1 F y * pdList p.2 g y)).sum :=
    cm_list_sum_apply Sf (fun p y => pdList p.1 F y * pdList p.2 g y)
  calc |L2re (fun x => pdList L (fun z => F z * g z) x - F x * pdList L g x) h|
      = |L2re ((Sf.map (fun p => fun y => pdList p.1 F y * pdList p.2 g y)).sum) h| := by
        rw [hleib, hfun]
    _ = |(Sf.map (fun p => L2re (fun y => pdList p.1 F y * pdList p.2 g y) h)).sum| := by rw [hlin]
    _ ≤ (Sf.length : ℝ) * (M * η * G + (M / (4 * η)) * H) := by
        rw [← hconst]; exact hsum
    _ ≤ ((splits L).length : ℝ) * (M * η * G + (M / (4 * η)) * H) :=
        mul_le_mul_of_nonneg_right hlenSf hB0


/-- Moving a single `pd` across a `pdList`, as an appended list. -/
lemma cm_pd_pdList_eq (i : ι) (q : List ι) (f : (ι → ℝ) → ℂ)
    (hf : ContDiff ℝ (((q.length + 1 : ℕ)) : WithTop ℕ∞) f) :
    pd i (pdList q f) = pdList (q ++ [i]) f := by
  rw [cm_pd_pdList_comm i q f hf]
  rw [cm_pdList_append q [i] f]
  rfl

/-- **Poincaré step.**  The mean-zero Poincaré inequality on the cube, applied to the iterated
derivatives of `f`, yields `ENormSq j f ≤ C (card ι + 1)⁽ᵏ⁺¹⁾ ENormSq (j+1) f`
for `1 ≤ j ≤ k`. -/
lemma cm_ENormSq_step (C : ℝ) (hC0 : 0 ≤ C)
    (hPoinc : ∀ f : (ι → ℝ) → ℂ, ContDiff ℝ 1 f → Periodic1 f →
      (∫ x in unitCube, f x = 0) →
      ∫ x in unitCube, ‖f x‖ ^ 2 ≤ C * ∑ i, ∫ x in unitCube, ‖pd i f x‖ ^ 2)
    (k j : ℕ) (hj : 1 ≤ j) (hjk : j ≤ k) (f : (ι → ℝ) → ℂ)
    (hf : ContDiff ℝ (((k + 1 : ℕ)) : WithTop ℕ∞) f) (hper : Periodic1 f) :
    ENormSq j f ≤ (C * ((Fintype.card ι : ℝ) + 1) ^ (k + 1)) * ENormSq (j + 1) f := by
  have hf' : ContDiff ℝ (((j + 1 : ℕ)) : WithTop ℕ∞) f := cm_of_le hf (by omega)
  have hper_l : ∀ l : Fin j → ι, Periodic1 (pdVec j l f) := by
    intro l i
    refine cm_periodicIn_pdList (List.ofFn l) f (fun q' hq' => ?_) hper i
    have hlen : q'.length + 1 ≤ j + 1 := by
      have h := List.Sublist.length_le hq'
      simpa using h
    exact (cm_contDiff_pdList q' 1 f (cm_of_le hf' (by omega))).differentiable (by norm_num)
  have hmean : ∀ l : Fin j → ι, ∫ x in unitCube, pdVec j l f x = 0 :=
    fun l => cm_integral_pdVec_eq_zero j l f hf' hper hj
  have hcd : ∀ l : Fin j → ι, ContDiff ℝ 1 (pdVec j l f) := by
    intro l
    have h1 : ContDiff ℝ ((((List.ofFn l).length + 1 : ℕ)) : WithTop ℕ∞) f := by simpa using hf'
    exact cm_contDiff_pdList (List.ofFn l) 1 f h1
  have hinner : ∀ l : Fin j → ι,
      ∫ x in unitCube, ‖pdVec j l f x‖ ^ 2
        ≤ C * ((Fintype.card ι : ℝ) * ENormSq (j + 1) f) := by
    intro l
    have hp := hPoinc (pdVec j l f) (hcd l) (hper_l l) (hmean l)
    refine hp.trans (mul_le_mul_of_nonneg_left ?_ hC0)
    calc ∑ i : ι, ∫ x in unitCube, ‖pd i (pdVec j l f) x‖ ^ 2
        = ∑ i : ι, ∫ x in unitCube, ‖pdList (List.ofFn l ++ [i]) f x‖ ^ 2 := by
          refine Finset.sum_congr rfl (fun i _ => ?_)
          rw [show pdVec j l f = pdList (List.ofFn l) f from rfl]
          rw [cm_pd_pdList_eq i (List.ofFn l) f (cm_of_le hf' (by simp))]
      _ ≤ ∑ _i : ι, ENormSq (j + 1) f := by
          refine Finset.sum_le_sum (fun i _ => ?_)
          refine le_trans (cm_integral_pdList_le_ENormSq (List.ofFn l ++ [i]) f) ?_
          rw [List.length_append, List.length_ofFn, List.length_cons, List.length_nil]
      _ = (Fintype.card ι : ℝ) * ENormSq (j + 1) f := by
          rw [Finset.sum_const, nsmul_eq_mul, Finset.card_univ]
  have hEnn : 0 ≤ ENormSq (j + 1) f := cm_ENormSq_nonneg _ _
  calc ENormSq j f = ∑ l : Fin j → ι, ∫ x in unitCube, ‖pdVec j l f x‖ ^ 2 := rfl
    _ ≤ ∑ _l : Fin j → ι, C * ((Fintype.card ι : ℝ) * ENormSq (j + 1) f) :=
        Finset.sum_le_sum (fun l _ => hinner l)
    _ = (Fintype.card (Fin j → ι) : ℝ) * (C * ((Fintype.card ι : ℝ) * ENormSq (j + 1) f)) := by
        rw [Finset.sum_const, nsmul_eq_mul, Finset.card_univ]
    _ ≤ (C * ((Fintype.card ι : ℝ) + 1) ^ (k + 1)) * ENormSq (j + 1) f := by
        rw [Fintype.card_fun, Fintype.card_fin]
        push_cast
        have hci : (0 : ℝ) ≤ (Fintype.card ι : ℝ) := by positivity
        have hCE : 0 ≤ C * ENormSq (j + 1) f := mul_nonneg hC0 hEnn
        have h2a : (Fintype.card ι : ℝ) ^ (j + 1) ≤ ((Fintype.card ι : ℝ) + 1) ^ (j + 1) :=
          pow_le_pow_left₀ hci (by linarith) _
        have h2b : ((Fintype.card ι : ℝ) + 1) ^ (j + 1) ≤ ((Fintype.card ι : ℝ) + 1) ^ (k + 1) :=
          pow_le_pow_right₀ (by linarith) (by omega)
        have h3 : (Fintype.card ι : ℝ) ^ j * (Fintype.card ι : ℝ)
            = (Fintype.card ι : ℝ) ^ (j + 1) := by rw [pow_succ]
        calc (Fintype.card ι : ℝ) ^ j * (C * ((Fintype.card ι : ℝ) * ENormSq (j + 1) f))
            = (C * ENormSq (j + 1) f) * ((Fintype.card ι : ℝ) ^ j * (Fintype.card ι : ℝ)) := by
              ring
          _ = (C * ENormSq (j + 1) f) * (Fintype.card ι : ℝ) ^ (j + 1) := by rw [h3]
          _ ≤ (C * ENormSq (j + 1) f) * ((Fintype.card ι : ℝ) + 1) ^ (k + 1) := by
              refine mul_le_mul_of_nonneg_left (le_trans h2a h2b) hCE
          _ = (C * ((Fintype.card ι : ℝ) + 1) ^ (k + 1)) * ENormSq (j + 1) f := by ring



/-- `cm_pdList_ofReal` for the smoothness index `(⊤ : ℕ∞)` of the main statement. -/
lemma cm_pdList_ofReal_smooth (q : List ι) (F : (ι → ℝ) → ℝ) (hF : ContDiff ℝ (⊤ : ℕ∞) F) :
    pdList q (fun y => (F y : ℂ)) = fun y => ((pdRList q F y : ℝ) : ℂ) := by
  induction q with
  | nil => rfl
  | cons i q ih =>
      have h : pdList (i :: q) (fun y => (F y : ℂ))
          = pd i (pdList q (fun y => (F y : ℂ))) := rfl
      rw [h, ih]
      funext x
      have h1 : ContDiff ℝ (((q.length + 1 : ℕ)) : WithTop ℕ∞) F :=
        hF.of_le (WithTop.coe_le_coe.mpr le_top)
      have hd : DifferentiableAt ℝ (pdRList q F) x :=
        (cm_contDiff_pdRList q 1 F h1).differentiable (by norm_num) |>.differentiableAt
      rw [ga_pd_ofReal i (pdRList q F) x hd]
      rfl

/-- The complexified coefficient function has differentiable iterated derivatives. -/
lemma cm_diff_pdList_ofReal (A : (ι → ℝ) → ℝ) (hA : ContDiff ℝ (⊤ : ℕ∞) A) (q : List ι) :
    Differentiable ℝ (pdList q (fun y => (A y : ℂ))) := by
  rw [cm_pdList_ofReal_smooth q A hA]
  exact Complex.ofRealCLM.differentiable.comp
    ((cm_contDiff_pdRList q 1 A
      (hA.of_le (WithTop.coe_le_coe.mpr le_top))).differentiable (by norm_num))

/-- The complexification is continuous after iterated derivatives. -/
lemma cm_cont_pdList_ofReal (A : (ι → ℝ) → ℝ) (hA : ContDiff ℝ (⊤ : ℕ∞) A) (q : List ι) :
    Continuous (pdList q (fun y => (A y : ℂ))) := by
  rw [cm_pdList_ofReal_smooth q A hA]
  exact Complex.ofRealCLM.continuous.comp
    ((cm_contDiff_pdRList q 0 A (hA.of_le (WithTop.coe_le_coe.mpr le_top))).continuous)

/-- The second derivative block of `u` is differentiable after `pdList q`, `q.length < k`. -/
lemma cm_diff_pdList_pair (k : ℕ) (u : (ι → ℝ) → ℂ)
    (hu : ContDiff ℝ (((k + 2 : ℕ)) : WithTop ℕ∞) u) (c d : ι) {q : List ι} (hq : q.length < k) :
    Differentiable ℝ (pdList q (fun z => pd c (pd d u) z)) := by
  rw [cm_pdList_pair q c d u]
  have h1 : ContDiff ℝ (((q.length + 2 + 1 : ℕ)) : WithTop ℕ∞) u := cm_of_le hu (by omega)
  refine (cm_contDiff_pdList (q ++ [c, d]) 1 u ?_).differentiable (by norm_num)
  have : (q ++ [c, d]).length + 1 = q.length + 2 + 1 := by simp
  rwa [this]

/-- Continuity of the second derivative block after `pdList q`, `q.length ≤ k`. -/
lemma cm_cont_pdList_pair (k : ℕ) (u : (ι → ℝ) → ℂ)
    (hu : ContDiff ℝ (((k + 2 : ℕ)) : WithTop ℕ∞) u) (c d : ι) {q : List ι} (hq : q.length ≤ k) :
    Continuous (pdList q (fun z => pd c (pd d u) z)) := by
  rw [cm_pdList_pair q c d u]
  have h1 : ContDiff ℝ (((q.length + 2 : ℕ)) : WithTop ℕ∞) u := cm_of_le hu (by omega)
  refine (cm_contDiff_pdList (q ++ [c, d]) 0 u ?_).continuous
  have : (q ++ [c, d]).length + 0 = q.length + 2 := by simp
  rwa [this]

/-- Smoothness of the product `A_{cd} · ∂_c∂_d u` after `pdList q`, `q.length < k`. -/
lemma cm_diff_pdList_mul (k : ℕ) (A : ι → ι → (ι → ℝ) → ℝ) (u : (ι → ℝ) → ℂ)
    (hA : ∀ c d, ContDiff ℝ (⊤ : ℕ∞) (A c d))
    (hu : ContDiff ℝ (((k + 2 : ℕ)) : WithTop ℕ∞) u)
    (p : ι × ι) {q : List ι} (hq : q.length < k) :
    Differentiable ℝ (pdList q (fun y => (A p.1 p.2 y : ℂ) * pd p.1 (pd p.2 u) y)) := by
  have hsmA : ContDiff ℝ (((q.length + 1 : ℕ)) : WithTop ℕ∞) (fun y => (A p.1 p.2 y : ℂ)) :=
    Complex.ofRealCLM.contDiff.comp ((hA p.1 p.2).of_le (WithTop.coe_le_coe.mpr le_top))
  have hsmg : ContDiff ℝ (((q.length + 1 : ℕ)) : WithTop ℕ∞) (pd p.1 (pd p.2 u)) := by
    have h1 : ContDiff ℝ ((([p.1, p.2]).length + (q.length + 1) : ℕ)) u :=
      cm_of_le hu (by simp; omega)
    exact cm_contDiff_pdList [p.1, p.2] (q.length + 1) u h1
  exact (cm_contDiff_pdList q 1 _ (hsmA.mul hsmg)).differentiable (by norm_num)

/-- Continuity of the product `A_{cd} · ∂_c∂_d u` after `pdList q`, `q.length ≤ k`. -/
lemma cm_cont_pdList_mul (k : ℕ) (A : ι → ι → (ι → ℝ) → ℝ) (u : (ι → ℝ) → ℂ)
    (hA : ∀ c d, ContDiff ℝ (⊤ : ℕ∞) (A c d))
    (hu : ContDiff ℝ (((k + 2 : ℕ)) : WithTop ℕ∞) u)
    (p : ι × ι) {q : List ι} (hq : q.length ≤ k) :
    Continuous (pdList q (fun y => (A p.1 p.2 y : ℂ) * pd p.1 (pd p.2 u) y)) := by
  have hsmA : ContDiff ℝ (((q.length : ℕ)) : WithTop ℕ∞) (fun y => (A p.1 p.2 y : ℂ)) :=
    Complex.ofRealCLM.contDiff.comp ((hA p.1 p.2).of_le (WithTop.coe_le_coe.mpr le_top))
  have hsmg : ContDiff ℝ (((q.length : ℕ)) : WithTop ℕ∞) (pd p.1 (pd p.2 u)) := by
    have h1 : ContDiff ℝ ((([p.1, p.2]).length + q.length : ℕ)) u :=
      cm_of_le hu (by simp; omega)
    exact cm_contDiff_pdList [p.1, p.2] q.length u h1
  exact (cm_contDiff_pdList q 0 _ (hsmA.mul hsmg)).continuous

/-- Bound on `‖∂^q(F)‖` through the real derivative bound. -/
lemma cm_norm_pdList_ofReal_le (A : (ι → ℝ) → ℝ) (hA : ContDiff ℝ (⊤ : ℕ∞) A) (q : List ι)
    (M : ℝ) (hM : ∀ x, |pdRList q A x| ≤ M) (x : ι → ℝ) :
    ‖pdList q (fun y => (A y : ℂ)) x‖ ≤ M := by
  rw [cm_pdList_ofReal_smooth q A hA]
  simpa using hM x


/-- The real partial derivative of a periodic function is periodic. -/
lemma cm_periodicIn_pdR (i j : ι) {F : (ι → ℝ) → ℝ} (hF : Differentiable ℝ F)
    (hper : PeriodicIn i F) : PeriodicIn i (pdR j F) := by
  intro x
  have hφ : fderiv ℝ (fun y : ι → ℝ => y + Pi.single i 1) x
      = ContinuousLinearMap.id ℝ (ι → ℝ) := by
    simp
  have hcomp : fderiv ℝ (fun y : ι → ℝ => F (y + Pi.single i 1)) x = fderiv ℝ F x := by
    rw [show (fun y : ι → ℝ => F (y + Pi.single i 1)) = F from funext hper]
  have h2 : fderiv ℝ (fun y : ι → ℝ => F (y + Pi.single i 1)) x
      = (fderiv ℝ F (x + Pi.single i 1)).comp
          (fderiv ℝ (fun y : ι → ℝ => y + Pi.single i 1) x) :=
    fderiv_comp x hF.differentiableAt (by fun_prop)
  rw [hcomp, hφ, ContinuousLinearMap.comp_id] at h2
  simp only [pdR]
  rw [← h2]

/-- `pdRList` of a smooth periodic function is periodic. -/
lemma cm_periodic1_pdRList (q : List ι) (F : (ι → ℝ) → ℝ) (hF : ContDiff ℝ (⊤ : ℕ∞) F)
    (hper : Periodic1 F) : Periodic1 (pdRList q F) := by
  induction q with
  | nil => exact hper
  | cons j q ih =>
      intro i
      have h1 : pdRList (j :: q) F = pdR j (pdRList q F) := rfl
      rw [h1]
      refine cm_periodicIn_pdR i j ?_ (ih i)
      exact (cm_contDiff_pdRList q 1 F (hF.of_le (WithTop.coe_le_coe.mpr le_top))).differentiable
        (by norm_num)

/-- A uniform bound for all iterated partial derivatives of order `≤ m` of a smooth periodic
real function.  (Version of `exists_bound_pdRList` for the smoothness index of the main
statement, `ContDiff ℝ (⊤ : ℕ∞)`.) -/
lemma cm_exists_bound_pdRList (m : ℕ) (F : (ι → ℝ) → ℝ) (hF : ContDiff ℝ (⊤ : ℕ∞) F)
    (hper : Periodic1 F) :
    ∃ M : ℝ, 0 ≤ M ∧ ∀ q : List ι, q.length ≤ m → ∀ x, |pdRList q F x| ≤ M := by
  have hb : ∀ j : ebJetIdx ι m, ∃ M : ℝ, 0 ≤ M ∧ ∀ x, |pdRList (List.ofFn j.2) F x| ≤ M := by
    intro j
    have hlen : (List.ofFn j.2).length ≤ m := by
      have := j.1.isLt
      simpa using Nat.lt_succ_iff.mp this
    refine eb_exists_bound_of_continuous_periodic1 ?_ ?_
    · exact (cm_contDiff_pdRList (List.ofFn j.2) 0 F
        (hF.of_le (WithTop.coe_le_coe.mpr le_top))).continuous
    · exact cm_periodic1_pdRList (List.ofFn j.2) F hF hper
  choose B hB0 hB using hb
  refine ⟨∑ j : ebJetIdx ι m, B j, Finset.sum_nonneg fun j _ => hB0 j, ?_⟩
  intro q hq x
  have h1 : B ⟨⟨q.length, by omega⟩, q.get⟩ ≤ ∑ j : ebJetIdx ι m, B j :=
    Finset.single_le_sum (fun j _ => hB0 j) (Finset.mem_univ _)
  have h2 := hB ⟨⟨q.length, by omega⟩, q.get⟩ x
  rw [List.ofFn_get] at h2
  exact le_trans h2 h1

end Work.Diff.STE
