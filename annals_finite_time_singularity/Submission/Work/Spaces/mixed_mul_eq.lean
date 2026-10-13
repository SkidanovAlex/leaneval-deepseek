import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv
import Submission.Work.Spaces.Defs
import Submission.Work.Spaces.MixedMulDefs
import Submission.Work.Spaces.DerivLikeDefs
import Submission.Work.Spaces.DerivLikeBasic
import Submission.Work.Spaces.mixed_comm

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section
open scoped Real Topology
open Set Filter

namespace Work.Spaces

set_option maxHeartbeats 1600000

/-! ## Differentiability of slices -/

lemma SmoothU.differentiableAt {F : ℝ × ℝ → ℝ} (h : SmoothU F) {p : ℝ × ℝ}
    (hp : p ∈ quadU) : DifferentiableAt ℝ F p :=
  (h.contDiffAt (isOpen_quadU.mem_nhds hp)).differentiableAt (by norm_num)

lemma differentiableAt_slice_fst {F : ℝ × ℝ → ℝ} {z θ : ℝ}
    (h : DifferentiableAt ℝ F (z, θ)) :
    DifferentiableAt ℝ (fun z' => F (z', θ)) z := by
  change DifferentiableAt ℝ (F ∘ fun z' : ℝ => (z', θ)) z
  exact h.comp z (hasFDerivAt_prodMk_left z θ).differentiableAt

lemma differentiableAt_slice_snd {F : ℝ × ℝ → ℝ} {z θ : ℝ}
    (h : DifferentiableAt ℝ F (z, θ)) :
    DifferentiableAt ℝ (fun θ' => F (z, θ')) θ := by
  change DifferentiableAt ℝ (F ∘ fun θ' : ℝ => (z, θ')) θ
  exact h.comp θ (hasFDerivAt_prodMk_right z θ).differentiableAt

/-! ## The derivation-like structure for `Zb` -/

theorem Zb_DerivLike : DerivLike quadU SmoothU Zb where
  add := fun A B hA hB => by
    rintro ⟨z, θ⟩ hp
    have hA' : DifferentiableAt ℝ (fun z' => A (z', θ)) z :=
      differentiableAt_slice_fst (hA.differentiableAt hp)
    have hB' : DifferentiableAt ℝ (fun z' => B (z', θ)) z :=
      differentiableAt_slice_fst (hB.differentiableAt hp)
    show Zb (A + B) (z, θ) = Zb A (z, θ) + Zb B (z, θ)
    simp only [Zb]
    rw [show (fun z' => (A + B) (z', θ)) =
          (fun z' => A (z', θ)) + (fun z' => B (z', θ)) from rfl,
        deriv_add hA' hB']
    ring
  mul := fun A B hA hB => by
    rintro ⟨z, θ⟩ hp
    have hA' : DifferentiableAt ℝ (fun z' => A (z', θ)) z :=
      differentiableAt_slice_fst (hA.differentiableAt hp)
    have hB' : DifferentiableAt ℝ (fun z' => B (z', θ)) z :=
      differentiableAt_slice_fst (hB.differentiableAt hp)
    show Zb (A * B) (z, θ) = Zb A (z, θ) * B (z, θ) + A (z, θ) * Zb B (z, θ)
    simp only [Zb]
    rw [show (fun z' => (A * B) (z', θ)) =
          (fun z' => A (z', θ)) * (fun z' => B (z', θ)) from rfl,
        deriv_mul hA' hB']
    ring
  congr := fun A B h => by
    rintro ⟨z, θ⟩ hp
    have hs : Set.EqOn (fun z' => A (z', θ)) (fun z' => B (z', θ)) (Set.Ioi (-1)) :=
      fun z' hz' => h ⟨hz', hp.2⟩
    show Zb A (z, θ) = Zb B (z, θ)
    simp only [Zb]
    rw [hs.deriv isOpen_Ioi hp.1]
  preserve := fun A hA => by
    have hfd : ContDiffOn ℝ ⊤ (fderiv ℝ A) quadU := hA.fderiv_of_isOpen isOpen_quadU (by simp)
    have hev : ContDiffOn ℝ ⊤ (fun p : ℝ × ℝ => (fderiv ℝ A p) (1, 0)) quadU :=
      hfd.clm_apply contDiffOn_const
    have hfun : ContDiffOn ℝ ⊤ (fun p : ℝ × ℝ => p.1 * (fderiv ℝ A p) (1, 0)) quadU :=
      (contDiff_fst.contDiffOn).mul hev
    refine hfun.congr (fun p hp => ?_)
    obtain ⟨z, θ⟩ := p
    dsimp only
    show Zb A (z, θ) = z * (fderiv ℝ A (z, θ)) (1, 0)
    simp only [Zb]
    rw [deriv_slice_fst A z θ (hA.differentiableAt hp)]
  smul := fun c A hA => by
    rintro ⟨z, θ⟩ hp
    have hA' : DifferentiableAt ℝ (fun z' => A (z', θ)) z :=
      differentiableAt_slice_fst (hA.differentiableAt hp)
    show Zb (fun p => c * A p) (z, θ) = c * Zb A (z, θ)
    simp only [Zb]
    rw [deriv_const_mul c hA']
    ring

/-! ## The derivation-like structure for `Tb` -/

theorem Tb_DerivLike : DerivLike quadU SmoothU Tb where
  add := fun A B hA hB => by
    rintro ⟨z, θ⟩ hp
    have hA' : DifferentiableAt ℝ (fun θ' => A (z, θ')) θ :=
      differentiableAt_slice_snd (hA.differentiableAt hp)
    have hB' : DifferentiableAt ℝ (fun θ' => B (z, θ')) θ :=
      differentiableAt_slice_snd (hB.differentiableAt hp)
    show Tb (A + B) (z, θ) = Tb A (z, θ) + Tb B (z, θ)
    simp only [Tb]
    rw [show (fun θ' => (A + B) (z, θ')) =
          (fun θ' => A (z, θ')) + (fun θ' => B (z, θ')) from rfl,
        deriv_add hA' hB']
    ring
  mul := fun A B hA hB => by
    rintro ⟨z, θ⟩ hp
    have hA' : DifferentiableAt ℝ (fun θ' => A (z, θ')) θ :=
      differentiableAt_slice_snd (hA.differentiableAt hp)
    have hB' : DifferentiableAt ℝ (fun θ' => B (z, θ')) θ :=
      differentiableAt_slice_snd (hB.differentiableAt hp)
    show Tb (A * B) (z, θ) = Tb A (z, θ) * B (z, θ) + A (z, θ) * Tb B (z, θ)
    simp only [Tb]
    rw [show (fun θ' => (A * B) (z, θ')) =
          (fun θ' => A (z, θ')) * (fun θ' => B (z, θ')) from rfl,
        deriv_mul hA' hB']
    ring
  congr := fun A B h => by
    rintro ⟨z, θ⟩ hp
    have hs : Set.EqOn (fun θ' => A (z, θ')) (fun θ' => B (z, θ')) (Set.Ioo 0 (π/2)) :=
      fun θ' hθ' => h ⟨hp.1, hθ'⟩
    show Tb A (z, θ) = Tb B (z, θ)
    simp only [Tb]
    rw [hs.deriv isOpen_Ioo hp.2]
  preserve := fun A hA => by
    have hfd : ContDiffOn ℝ ⊤ (fderiv ℝ A) quadU := hA.fderiv_of_isOpen isOpen_quadU (by simp)
    have hev : ContDiffOn ℝ ⊤ (fun p : ℝ × ℝ => (fderiv ℝ A p) (0, 1)) quadU :=
      hfd.clm_apply contDiffOn_const
    have hsin : ContDiffOn ℝ ⊤ (fun p : ℝ × ℝ => Real.sin (2 * p.2)) quadU :=
      (Real.contDiff_sin.comp (contDiff_const.mul contDiff_snd)).contDiffOn
    have hfun : ContDiffOn ℝ ⊤
        (fun p : ℝ × ℝ => Real.sin (2 * p.2) * (fderiv ℝ A p) (0, 1)) quadU :=
      hsin.mul hev
    refine hfun.congr (fun p hp => ?_)
    obtain ⟨z, θ⟩ := p
    dsimp only
    show Tb A (z, θ) = Real.sin (2 * θ) * (fderiv ℝ A (z, θ)) (0, 1)
    simp only [Tb]
    rw [deriv_slice_snd A z θ (hA.differentiableAt hp)]
  smul := fun c A hA => by
    rintro ⟨z, θ⟩ hp
    have hA' : DifferentiableAt ℝ (fun θ' => A (z, θ')) θ :=
      differentiableAt_slice_snd (hA.differentiableAt hp)
    show Tb (fun p => c * A p) (z, θ) = c * Tb A (z, θ)
    simp only [Tb]
    rw [deriv_const_mul c hA']
    ring

/-! ## The derivation-like structure for `Zop` -/

theorem Zop_DerivLike : DerivLike (Set.Ioi (-1)) SmoothZ Zop where
  add := fun A B hA hB => by
    intro z hz
    have hA' : DifferentiableAt ℝ A z :=
      (hA.contDiffAt (isOpen_Ioi.mem_nhds hz)).differentiableAt (by norm_num)
    have hB' : DifferentiableAt ℝ B z :=
      (hB.contDiffAt (isOpen_Ioi.mem_nhds hz)).differentiableAt (by norm_num)
    show Zop (A + B) z = Zop A z + Zop B z
    simp only [Zop]
    rw [deriv_add hA' hB']
    ring
  mul := fun A B hA hB => by
    intro z hz
    have hA' : DifferentiableAt ℝ A z :=
      (hA.contDiffAt (isOpen_Ioi.mem_nhds hz)).differentiableAt (by norm_num)
    have hB' : DifferentiableAt ℝ B z :=
      (hB.contDiffAt (isOpen_Ioi.mem_nhds hz)).differentiableAt (by norm_num)
    show Zop (A * B) z = Zop A z * B z + A z * Zop B z
    simp only [Zop]
    rw [deriv_mul hA' hB']
    ring
  congr := fun A B h => by
    intro z hz
    show Zop A z = Zop B z
    simp only [Zop]
    rw [h.deriv isOpen_Ioi hz]
  preserve := fun A hA => by
    have hfd : ContDiffOn ℝ ⊤ (fderiv ℝ A) (Set.Ioi (-1)) :=
      hA.fderiv_of_isOpen isOpen_Ioi (by simp)
    have hev : ContDiffOn ℝ ⊤ (fun z : ℝ => (fderiv ℝ A z) 1) (Set.Ioi (-1)) :=
      hfd.clm_apply contDiffOn_const
    have hfun : ContDiffOn ℝ ⊤ (fun z : ℝ => z * (fderiv ℝ A z) 1) (Set.Ioi (-1)) :=
      (contDiff_id.contDiffOn).mul hev
    refine hfun.congr (fun z hz => ?_)
    show Zop A z = z * (fderiv ℝ A z) 1
    simp only [Zop]
    rw [fderiv_apply_one_eq_deriv]
  smul := fun c A hA => by
    intro z hz
    have hA' : DifferentiableAt ℝ A z :=
      (hA.contDiffAt (isOpen_Ioi.mem_nhds hz)).differentiableAt (by norm_num)
    show Zop (fun p => c * A p) z = c * Zop A z
    simp only [Zop]
    rw [deriv_const_mul c hA']
    ring

/-! ## Translations between the uncurried operators and `Dz`, `Dth` -/

lemma Zb_uncurry (f : ℝ → ℝ → ℝ) :
    Zb (Function.uncurry f) = Function.uncurry (Dz f) := by
  funext p
  simp only [Zb, Dz, pz, Function.uncurry]

lemma Tb_uncurry (f : ℝ → ℝ → ℝ) :
    Tb (Function.uncurry f) = Function.uncurry (Dth f) := by
  funext p
  simp only [Tb, Dth, pth, Function.uncurry]

lemma Zb_iterate_uncurry (n : ℕ) (f : ℝ → ℝ → ℝ) :
    Zb^[n] (Function.uncurry f) = Function.uncurry (DzIter n f) := by
  induction n with
  | zero => rfl
  | succ n ih =>
      rw [Function.iterate_succ_apply', ih, Zb_uncurry]
      rfl

lemma Tb_iterate_uncurry (n : ℕ) (f : ℝ → ℝ → ℝ) :
    Tb^[n] (Function.uncurry f) = Function.uncurry (DthIter n f) := by
  induction n with
  | zero => rfl
  | succ n ih =>
      rw [Function.iterate_succ_apply', ih, Tb_uncurry]
      rfl

lemma uncurry_mul (f g : ℝ → ℝ → ℝ) :
    Function.uncurry f * Function.uncurry g = Function.uncurry (fun z θ => f z θ * g z θ) :=
  rfl

lemma Zop_slice (n : ℕ) (f : ℝ → ℝ → ℝ) (θ : ℝ) :
    (fun z => DzIter n f z θ) = Zop^[n] (fun z => f z θ) := by
  induction n with
  | zero => rfl
  | succ n ih =>
      funext z
      rw [Function.iterate_succ_apply']
      show Dz (DzIter n f) z θ = Zop (Zop^[n] (fun z => f z θ)) z
      simp only [Dz, pz, Zop]
      rw [ih]

/-! ## Leibniz for `D_z` alone (used on the angular boundary) -/

theorem DzIter_mul (j : ℕ) (f g : ℝ → ℝ → ℝ) {z θ : ℝ} (hz : z ∈ Iz)
    (hf : ContDiffOn ℝ ⊤ (fun z => f z θ) (Set.Ioi (-1)))
    (hg : ContDiffOn ℝ ⊤ (fun z => g z θ) (Set.Ioi (-1))) :
    DzIter j (fun z θ => f z θ * g z θ) z θ =
      ∑ b ∈ Finset.range (j + 1),
        (j.choose b : ℝ) * (DzIter b f z θ * DzIter (j - b) g z θ) := by
  have hz1 : z ∈ Set.Ioi (-1) := by
    rw [Iz, Set.mem_Ici] at hz
    rw [Set.mem_Ioi]; linarith
  have key := (DerivLike.iterate_mul Zop_DerivLike SmoothZ_FunClass j hf hg) hz1
  rw [show (fun z => f z θ) * (fun z => g z θ) = (fun z => f z θ * g z θ) from rfl] at key
  have htr : Zop^[j] (fun z => (fun z θ => f z θ * g z θ) z θ) z =
      Zop^[j] (fun z => f z θ * g z θ) z := rfl
  rw [congrFun (Zop_slice j (fun z θ => f z θ * g z θ) θ) z, htr, key]
  apply Finset.sum_congr rfl
  intro b hb
  rw [← congrFun (Zop_slice b f θ) z, ← congrFun (Zop_slice (j - b) g θ) z]

/-! ## The general two-operator iterated Leibniz rule -/

theorem DerivLike.twoOp_iterate_mul {X : Type*} {s : Set X} {P : (X → ℝ) → Prop}
    {Z Θb : (X → ℝ) → (X → ℝ)} (hP : FunClass P)
    (hZ : DerivLike s P Z) (hΘ : DerivLike s P Θb) (m n : ℕ) {F G : X → ℝ}
    (hF : P F) (hG : P G) :
    Set.EqOn (Z^[m] (Θb^[n] (F * G)))
      (fun p => ∑ a ∈ Finset.range (n + 1), ∑ b ∈ Finset.range (m + 1),
        ((n.choose a : ℝ) * (m.choose b : ℝ)) *
          ((Z^[b] (Θb^[a] F)) p * (Z^[m - b] (Θb^[n - a] G)) p)) s := by
  have hA : ∀ a ≤ n, P (fun p => (n.choose a : ℝ) *
      ((Θb^[a] F) p * (Θb^[n - a] G) p)) := fun a ha =>
    hP.smul _ _ (hP.mul _ _ (hΘ.preserve_iterate a hF) (hΘ.preserve_iterate (n - a) hG))
  have step1 : Set.EqOn (Z^[m] (Θb^[n] (F * G)))
      (Z^[m] (fun p => ∑ a ∈ Finset.range (n + 1),
        (n.choose a : ℝ) * ((Θb^[a] F) p * (Θb^[n - a] G) p))) s :=
    hZ.iterate_congr m (hΘ.iterate_mul hP n hF hG)
  have step2 : Set.EqOn
      (Z^[m] (fun p => ∑ a ∈ Finset.range (n + 1),
        (n.choose a : ℝ) * ((Θb^[a] F) p * (Θb^[n - a] G) p)))
      (fun p => ∑ a ∈ Finset.range (n + 1),
        (Z^[m] (fun p => (n.choose a : ℝ) *
          ((Θb^[a] F) p * (Θb^[n - a] G) p))) p) s :=
    hZ.iterate_sum_range hP m n hA
  have step3 : ∀ a ≤ n, Set.EqOn
      (Z^[m] (fun p => (n.choose a : ℝ) * ((Θb^[a] F) p * (Θb^[n - a] G) p)))
      (fun p => ∑ b ∈ Finset.range (m + 1), ((n.choose a : ℝ) * (m.choose b : ℝ)) *
        ((Z^[b] (Θb^[a] F)) p * (Z^[m - b] (Θb^[n - a] G)) p)) s := by
    intro a ha
    have hFa : P (Θb^[a] F) := hΘ.preserve_iterate a hF
    have hGa : P (Θb^[n - a] G) := hΘ.preserve_iterate (n - a) hG
    have hB : P ((Θb^[a] F) * (Θb^[n - a] G)) := hP.mul _ _ hFa hGa
    have hsm := hZ.iterate_smul m (n.choose a : ℝ) hB
    have hmul := hZ.iterate_mul hP m hFa hGa
    have hmul' := eqOn_const_mul (n.choose a : ℝ) hmul
    have hconv : Set.EqOn
        (fun p => (n.choose a : ℝ) * (∑ b ∈ Finset.range (m + 1),
          (m.choose b : ℝ) * ((Z^[b] (Θb^[a] F)) p * (Z^[m - b] (Θb^[n - a] G)) p)))
        (fun p => ∑ b ∈ Finset.range (m + 1), ((n.choose a : ℝ) * (m.choose b : ℝ)) *
          ((Z^[b] (Θb^[a] F)) p * (Z^[m - b] (Θb^[n - a] G)) p)) s := by
      intro p hp
      change (n.choose a : ℝ) * (∑ b ∈ Finset.range (m + 1),
          (m.choose b : ℝ) * ((Z^[b] (Θb^[a] F)) p * (Z^[m - b] (Θb^[n - a] G)) p)) =
        ∑ b ∈ Finset.range (m + 1), ((n.choose a : ℝ) * (m.choose b : ℝ)) *
          ((Z^[b] (Θb^[a] F)) p * (Z^[m - b] (Θb^[n - a] G)) p)
      rw [Finset.mul_sum]
      exact Finset.sum_congr rfl (fun b hb => by ring)
    exact hsm.trans (hmul'.trans hconv)
  have step4 : Set.EqOn
      (fun p => ∑ a ∈ Finset.range (n + 1),
        (Z^[m] (fun p => (n.choose a : ℝ) *
          ((Θb^[a] F) p * (Θb^[n - a] G) p))) p)
      (fun p => ∑ a ∈ Finset.range (n + 1), ∑ b ∈ Finset.range (m + 1),
        ((n.choose a : ℝ) * (m.choose b : ℝ)) *
          ((Z^[b] (Θb^[a] F)) p * (Z^[m - b] (Θb^[n - a] G)) p)) s :=
    eqOn_sum (Finset.range (n + 1))
      (fun a ha => step3 a (Nat.lt_succ_iff.mp (Finset.mem_range.mp ha)))
  exact step1.trans (step2.trans step4)

/-! ## The endpoints of the angular interval -/

lemma sin_two_eq_zero_of_not_Ioo {θ : ℝ} (hθ : θ ∈ Iθ) (h : θ ∉ Set.Ioo 0 (π/2)) :
    Real.sin (2 * θ) = 0 := by
  rw [Iθ, Set.mem_Icc] at hθ
  rcases lt_or_ge 0 θ with h0 | h0
  · rcases lt_or_ge θ (π/2) with h1 | h1
    · exact absurd (show θ ∈ Set.Ioo 0 (π/2) from ⟨h0, h1⟩) h
    · have h2 : θ = π / 2 := le_antisymm hθ.2 h1
      rw [h2]
      have h3 : 2 * (π / 2) = π := by ring
      rw [h3, Real.sin_pi]
  · have h2 : θ = 0 := le_antisymm h0 hθ.1
    rw [h2]; simp

lemma DthIter_eq_zero_of_sin {u : ℝ → ℝ → ℝ} {θ : ℝ} (h : Real.sin (2 * θ) = 0) :
    ∀ n, 1 ≤ n → ∀ z, DthIter n u z θ = 0 := by
  intro n
  induction n with
  | zero => intro hn; omega
  | succ n _ =>
      intro _ z
      show Dth (DthIter n u) z θ = 0
      show Real.sin (2 * θ) * pth (DthIter n u) z θ = 0
      rw [h, zero_mul]

lemma DzIter_eq_zero_of_slice_zero {u : ℝ → ℝ → ℝ} {θ : ℝ} (h : ∀ z, u z θ = 0) :
    ∀ j z, DzIter j u z θ = 0 := by
  intro j
  induction j with
  | zero => intro z; exact h z
  | succ j ih =>
      intro z
      show Dz (DzIter j u) z θ = 0
      show z * deriv (fun z' => DzIter j u z' θ) z = 0
      rw [show (fun z' => DzIter j u z' θ) = fun _ => (0 : ℝ) from funext (fun z' => ih z')]
      simp

theorem mixed_mul_eq (j i : ℕ) (f g : ℝ → ℝ → ℝ)
    (hf : Work.Spaces.SmoothInt f) (hg : Work.Spaces.SmoothInt g) :
    ∀ z ∈ Work.Spaces.Iz, ∀ θ ∈ Work.Spaces.Iθ,
      Work.Spaces.mixed j i (fun z θ => f z θ * g z θ) z θ
        = ∑ a ∈ Finset.range (i + 1), ∑ b ∈ Finset.range (j + 1),
            ((i.choose a : ℝ) * (j.choose b : ℝ))
              * (Work.Spaces.mixed b a f z θ * Work.Spaces.mixed (j - b) (i - a) g z θ) := by
  intro z hz θ hθ
  rcases Nat.eq_zero_or_pos i with hi | hi
  · subst hi
    simp only [mixed_zero_right]
    rw [DzIter_mul j f g hz (hf.2 θ hθ) (hg.2 θ hθ)]
    rw [Finset.sum_range_one]
    simp
  · by_cases hcase : θ ∈ Set.Ioo 0 (π/2)
    · -- interior: the two-operator Leibniz rule
      have hz1 : z ∈ Set.Ioi (-1) := by
        rw [Iz, Set.mem_Ici] at hz
        rw [Set.mem_Ioi]; linarith
      have hp : (z, θ) ∈ quadU := ⟨hz1, hcase⟩
      have h2 := (DerivLike.twoOp_iterate_mul (X := ℝ × ℝ) (s := quadU) (P := SmoothU)
          SmoothU_FunClass Zb_DerivLike Tb_DerivLike j i
          (show SmoothU (Function.uncurry f) from hf.1)
          (show SmoothU (Function.uncurry g) from hg.1)) hp
      have h2' : Zb^[j] (Tb^[i] (Function.uncurry f * Function.uncurry g)) (z, θ)
          = ∑ a ∈ Finset.range (i + 1), ∑ b ∈ Finset.range (j + 1),
              ((i.choose a : ℝ) * (j.choose b : ℝ))
                * ((Zb^[b] (Tb^[a] (Function.uncurry f))) (z, θ)
                   * (Zb^[j - b] (Tb^[i - a] (Function.uncurry g))) (z, θ)) := by
        simpa using h2
      have hL : Zb^[j] (Tb^[i] (Function.uncurry f * Function.uncurry g)) (z, θ)
          = mixed j i (fun z θ => f z θ * g z θ) z θ := by
        rw [uncurry_mul f g, Tb_iterate_uncurry i (fun z θ => f z θ * g z θ),
            Zb_iterate_uncurry j (DthIter i (fun z θ => f z θ * g z θ))]
        rfl
      have e_f : ∀ a b, Zb^[b] (Tb^[a] (Function.uncurry f)) (z, θ) = mixed b a f z θ :=
        fun a b => by
          rw [Tb_iterate_uncurry a f, Zb_iterate_uncurry b (DthIter a f)]
          rfl
      have e_g : ∀ a b, Zb^[b] (Tb^[a] (Function.uncurry g)) (z, θ) = mixed b a g z θ :=
        fun a b => by
          rw [Tb_iterate_uncurry a g, Zb_iterate_uncurry b (DthIter a g)]
          rfl
      rw [← hL, h2']
      apply Finset.sum_congr rfl; intro a ha
      apply Finset.sum_congr rfl; intro b hb
      rw [e_f a b, e_g (i - a) (j - b)]
    · -- angular boundary: everything vanishes
      have hsin : Real.sin (2 * θ) = 0 := sin_two_eq_zero_of_not_Ioo hθ hcase
      have hL : mixed j i (fun z θ => f z θ * g z θ) z θ = 0 := by
        show DzIter j (DthIter i (fun z θ => f z θ * g z θ)) z θ = 0
        apply DzIter_eq_zero_of_slice_zero
        intro z'
        exact DthIter_eq_zero_of_sin hsin i hi z'
      have hR : (∑ a ∈ Finset.range (i + 1), ∑ b ∈ Finset.range (j + 1),
            ((i.choose a : ℝ) * (j.choose b : ℝ))
              * (mixed b a f z θ * mixed (j - b) (i - a) g z θ)) = 0 := by
        apply Finset.sum_eq_zero
        intro a ha
        apply Finset.sum_eq_zero
        intro b hb
        by_cases ha0 : a = 0
        · have hia : 1 ≤ i - a := by omega
          have hz0 : mixed (j - b) (i - a) g z θ = 0 := by
            show DzIter (j - b) (DthIter (i - a) g) z θ = 0
            apply DzIter_eq_zero_of_slice_zero
            intro z'
            exact DthIter_eq_zero_of_sin hsin (i - a) hia z'
          simp [hz0]
        · have ha1 : 1 ≤ a := by omega
          have hz0 : mixed b a f z θ = 0 := by
            show DzIter b (DthIter a f) z θ = 0
            apply DzIter_eq_zero_of_slice_zero
            intro z'
            exact DthIter_eq_zero_of_sin hsin a ha1 z'
          simp [hz0]
      rw [hL, hR]

end Work.Spaces
