import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.CStarAlgebra.Classes
import Mathlib.Analysis.Complex.CoveringMap
import Mathlib.Analysis.Convex.Contractible
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Topology.Algebra.Module.ModuleTopology
import Mathlib.Topology.Homotopy.Lifting

namespace Commons.Topology.Strip

open Set

noncomputable section

namespace PathShift


/-- coordinate map ℝ×ℝ → ℂ -/
def toc (q : ℝ × ℝ) : ℂ := (q.1 : ℂ) + (q.2 : ℂ) * Complex.I

lemma toc_re (q : ℝ × ℝ) : (toc q).re = q.1 := by simp [toc]
lemma toc_im (q : ℝ × ℝ) : (toc q).im = q.2 := by simp [toc]

lemma toc_inj : Function.Injective toc := by
  intro q q' h
  exact Prod.ext (by rw [← toc_re q, ← toc_re q', h]) (by rw [← toc_im q, ← toc_im q', h])

lemma toc_cont : Continuous toc := by unfold toc; fun_prop

/-- clamp to [0,1] -/
def sig (u : ℝ) : ℝ := (Set.projIcc (0:ℝ) 1 (by norm_num) u : ℝ)

lemma sig_cont : Continuous sig := by
  unfold sig
  exact continuous_subtype_val.comp continuous_projIcc

lemma sig_mem (u : ℝ) : sig u ∈ Set.Icc (0:ℝ) 1 := (Set.projIcc (0:ℝ) 1 (by norm_num) u).2

lemma sig_of_mem {u : ℝ} (h : u ∈ Set.Icc (0:ℝ) 1) : sig u = u := by
  unfold sig
  rw [Set.coe_projIcc, min_eq_right h.2, max_eq_right h.1]

/-- two-edge path from (1,1) to (0,0) through (0,1) -/
def pp (u : ℝ) : ℝ × ℝ := (max (1 - 2 * sig u) 0, min 1 (2 - 2 * sig u))

lemma pp_cont : Continuous pp := by
  unfold pp
  refine Continuous.prodMk ?_ ?_
  · exact ((continuous_const.sub (continuous_const.mul sig_cont)).max continuous_const)
  · exact (continuous_const.min (continuous_const.sub (continuous_const.mul sig_cont)))

/-- diagonal path from (1,1) to (0,0) -/
def dd (u : ℝ) : ℝ × ℝ := (1 - sig u, 1 - sig u)

lemma dd_cont : Continuous dd := by
  unfold dd
  exact Continuous.prodMk (continuous_const.sub sig_cont) (continuous_const.sub sig_cont)

/-- convex interpolation between the two-edge path and the diagonal -/
def Pp (x : ℝ × ℝ) : ℝ × ℝ := (1 - sig x.1) • pp x.2 + (sig x.1) • dd x.2

lemma Pp_cont : Continuous Pp := by
  unfold Pp
  refine Continuous.add ?_ ?_
  · exact (continuous_const.sub (sig_cont.comp continuous_fst)).smul (pp_cont.comp continuous_snd)
  · exact ((sig_cont.comp continuous_fst)).smul (dd_cont.comp continuous_snd)

lemma sig_zero : sig 0 = 0 := by rw [sig, Set.coe_projIcc]; norm_num
lemma sig_one : sig 1 = 1 := by rw [sig, Set.coe_projIcc]; norm_num
lemma sig_half : sig (1/2) = 1/2 := by rw [sig, Set.coe_projIcc]; norm_num

lemma pp_zero : pp 0 = (1,1) := by simp only [pp, sig_zero]; norm_num
lemma pp_half : pp (1/2) = (0,1) := by simp only [pp, sig_half]; norm_num
lemma pp_one : pp 1 = (0,0) := by simp only [pp, sig_one]; norm_num

lemma dd_zero : dd 0 = (1,1) := by simp [dd, sig_zero]
lemma dd_one : dd 1 = (0,0) := by simp [dd, sig_one]

lemma Pp_fst_zero (u : ℝ) : Pp (0, u) = pp u := by simp [Pp, sig_zero]
lemma Pp_fst_one (u : ℝ) : Pp (1, u) = dd u := by simp [Pp, sig_one]
lemma Pp_snd_zero (s : ℝ) : Pp (s, 0) = (1,1) := by simp [Pp, pp_zero, dd_zero]
lemma Pp_snd_one (s : ℝ) : Pp (s, 1) = (0,0) := by simp [Pp, pp_one, dd_one]

lemma pp_left {u : ℝ} (hu : u ∈ Set.Icc (0:ℝ) (1/2)) : pp u = (1 - 2*u, 1) := by
  have h1 : sig u = u := sig_of_mem ⟨hu.1, by linarith [hu.2]⟩
  rw [pp, h1]
  have h2 : max (1 - 2*u) 0 = 1 - 2*u := max_eq_left (by linarith [hu.2])
  have h3 : min 1 (2 - 2*u) = 1 := min_eq_left (by linarith [hu.2])
  rw [h2, h3]

lemma pp_right {u : ℝ} (hu : u ∈ Set.Icc (0:ℝ) (1/2)) : pp (u + 1/2) = (0, 1 - 2*u) := by
  have h1 : sig (u + 1/2) = u + 1/2 := sig_of_mem ⟨by linarith [hu.1], by linarith [hu.2]⟩
  rw [pp, h1]
  have h2 : max (1 - 2*(u+1/2)) 0 = 0 := by
    rw [show 1 - 2*(u+1/2) = -2*u by ring, max_eq_right]; linarith [hu.1]
  have h3 : min 1 (2 - 2*(u+1/2)) = 1 - 2*u := by
    rw [show 2 - 2*(u+1/2) = 1 - 2*u by ring, min_eq_right]; linarith [hu.1]
  rw [h2, h3]

/-- staircase region {0 ≤ s ≤ t ≤ 1} -/
def Tm : Set (ℝ × ℝ) := {x : ℝ × ℝ | 0 ≤ x.1 ∧ x.1 ≤ x.2 ∧ x.2 ≤ 1}

lemma convex_Tm : Convex ℝ Tm := by
  rintro x ⟨hx1, hx2, hx3⟩ y ⟨hy1, hy2, hy3⟩ a b ha hb hab
  simp only [Tm, Set.mem_setOf_eq]
  refine ⟨?_, ?_, ?_⟩
  · have hxf : (a • x + b • y).1 = a * x.1 + b * y.1 := by simp
    rw [hxf]; nlinarith
  · have hxf : (a • x + b • y).1 = a * x.1 + b * y.1 := by simp
    have hxs : (a • x + b • y).2 = a * x.2 + b * y.2 := by simp
    rw [hxf, hxs]; nlinarith
  · have hxs : (a • x + b • y).2 = a * x.2 + b * y.2 := by simp
    rw [hxs]; nlinarith

lemma dd_mem (u : ℝ) : dd u ∈ Tm := by
  obtain ⟨h1, h2⟩ := sig_mem u
  simp only [Tm, Set.mem_setOf_eq, dd]
  exact ⟨by linarith, le_rfl, by linarith⟩

lemma pp_mem (u : ℝ) : pp u ∈ Tm := by
  obtain ⟨h1, h2⟩ := sig_mem u
  simp only [Tm, Set.mem_setOf_eq, pp]
  refine ⟨le_max_right _ _, ?_, min_le_left _ _⟩
  rw [max_le_iff]
  exact ⟨le_min (by linarith) (by linarith), le_min (by norm_num) (by linarith)⟩

lemma Pp_mem (x : ℝ × ℝ) : Pp x ∈ Tm := by
  have h1 : (0:ℝ) ≤ 1 - sig x.1 := by have := (sig_mem x.1).2; linarith
  have h2 : (0:ℝ) ≤ sig x.1 := (sig_mem x.1).1
  have h3 : (1 - sig x.1) + sig x.1 = 1 := by ring
  have := convex_Tm (pp_mem x.2) (dd_mem x.2) (a := 1 - sig x.1) (b := sig x.1) h1 h2 h3
  simpa [Pp] using this

lemma const_of_mem_zmultiples {c : ℂ} {f : ℝ → ℂ} (hf : Continuous f)
    (h : ∀ t, f t ∈ AddSubgroup.zmultiples c) : ∀ t, f t = f 0 := by
  set g : ℝ → ↥(AddSubgroup.zmultiples c) := fun t => ⟨f t, h t⟩ with hg
  have hgc : Continuous g := Continuous.subtype_mk hf h
  intro t
  have key : g t = g 0 := PreconnectedSpace.constant (α := ℝ)
      (Y := ↥(AddSubgroup.zmultiples c)) (inferInstance : PreconnectedSpace ℝ) hgc
  exact congrArg Subtype.val key

lemma path_shift_meets_planar (p : ℝ) (hp : 0 < p)
    (γ : C(Set.Icc (0:ℝ) 1, ℝ × ℝ)) (hγ1 : γ 1 = ((γ 0).1 + 2 * p, (γ 0).2)) :
    ∃ s t : Set.Icc (0:ℝ) 1, γ s = ((γ t).1 - p, (γ t).2) := by
  classical
  have h01 : (0:ℝ) ≤ 1 := by norm_num
  set g : ℝ → ℂ := fun u => toc (γ (Set.projIcc 0 1 h01 u)) with hgdef
  have hgc : Continuous g := toc_cont.comp (γ.continuous.comp continuous_projIcc)
  have hg0 : g 0 = toc (γ 0) := by
    simp only [hgdef]
    have h0 : (Set.projIcc 0 1 h01 (0:ℝ)) = (0 : Set.Icc (0:ℝ) 1) := by
      apply Subtype.ext; rw [Set.coe_projIcc]; norm_num
    rw [h0]
  have hg1 : g 1 = toc (γ 0) + (2 * p : ℂ) := by
    simp only [hgdef]
    have hz : (Set.projIcc 0 1 h01 (1:ℝ)) = (1 : Set.Icc (0:ℝ) 1) := by
      apply Subtype.ext; rw [Set.coe_projIcc]; norm_num
    rw [hz]
    show toc (γ 1) = toc (γ 0) + (2 * p : ℂ)
    rw [hγ1, toc, toc]
    push_cast
    ring
  set G : ℝ × ℝ → ℂ := fun x => g x.1 - g x.2 + (p : ℂ) with hGdef
  have hGcont : Continuous G := by rw [hGdef]; fun_prop
  by_cases hzero : ∃ x ∈ Tm, G x = 0
  · obtain ⟨x, hxT, hx0⟩ := hzero
    have hx1mem : x.1 ∈ Set.Icc (0:ℝ) 1 := ⟨hxT.1, le_trans hxT.2.1 hxT.2.2⟩
    have hx2mem : x.2 ∈ Set.Icc (0:ℝ) 1 := ⟨le_trans hxT.1 hxT.2.1, hxT.2.2⟩
    have hgx1 : g x.1 = toc (γ ⟨x.1, hx1mem⟩) := by
      simp only [hgdef]
      have : (Set.projIcc 0 1 h01 x.1) = (⟨x.1, hx1mem⟩ : Set.Icc (0:ℝ) 1) := by
        apply Subtype.ext
        show (Set.projIcc 0 1 h01 x.1 : ℝ) = x.1
        rw [Set.coe_projIcc, min_eq_right hx1mem.2, max_eq_right hx1mem.1]
      rw [this]
    have hgx2 : g x.2 = toc (γ ⟨x.2, hx2mem⟩) := by
      simp only [hgdef]
      have : (Set.projIcc 0 1 h01 x.2) = (⟨x.2, hx2mem⟩ : Set.Icc (0:ℝ) 1) := by
        apply Subtype.ext
        show (Set.projIcc 0 1 h01 x.2 : ℝ) = x.2
        rw [Set.coe_projIcc, min_eq_right hx2mem.2, max_eq_right hx2mem.1]
      rw [this]
    have hzero' : toc (γ ⟨x.1, hx1mem⟩) = toc (γ ⟨x.2, hx2mem⟩) - (p : ℂ) := by
      have h := hx0
      simp only [hGdef] at h
      rw [hgx1, hgx2] at h
      linear_combination h
    refine ⟨⟨x.1, hx1mem⟩, ⟨x.2, hx2mem⟩, ?_⟩
    apply toc_inj
    rw [hzero']
    rw [toc, toc]
    push_cast
    ring
  · have hno : ∀ x, x ∈ Tm → G x ≠ 0 := by
      intro x hx hcon; exact hzero ⟨x, hx, hcon⟩
    set c : ℝ → ℂ := fun u => G (pp u) with hcdef
    have hcne : ∀ u, c u ≠ 0 := fun u => by
      rw [hcdef]; exact hno (pp u) (pp_mem u)
    have hGanti : ∀ t : ℝ, G (0,t) = - G (t,1) := by
      intro t
      simp only [hGdef]
      rw [hg0, hg1]
      ring
    have hrel : ∀ u ∈ Set.Icc (0:ℝ) (1/2), c (u+1/2) = - c u := by
      intro u hu
      simp only [hcdef, pp_right hu, pp_left hu]
      exact hGanti (1 - 2*u)
    set Hm : C(ℝ × ℝ, {z : ℂ // z ≠ 0}) :=
      ⟨fun x => ⟨G (Pp x), hno (Pp x) (Pp_mem x)⟩,
        Continuous.subtype_mk (hGcont.comp Pp_cont) (fun x => hno (Pp x) (Pp_mem x))⟩ with hHmdef
    have hHmval : ∀ x, (Hm x : ℂ) = G (Pp x) := by intro x; rw [hHmdef]; rfl
    set e0 : ℂ := Complex.log ((Hm (0,0) : ℂ)) with he0def
    have he0 : (⟨Complex.exp e0, Complex.exp_ne_zero e0⟩ : {z : ℂ // z ≠ 0}) = Hm (0,0) := by
      apply Subtype.ext
      show Complex.exp e0 = (Hm (0,0) : ℂ)
      rw [he0def]
      exact Complex.exp_log (Hm (0,0)).2
    obtain ⟨F, ⟨hF0, hFlift⟩, -⟩ := IsCoveringMap.existsUnique_continuousMap_lifts
      Complex.isCoveringMap_exp Hm (0,0) e0 he0
    have hFlift' : ∀ x, Complex.exp (F x) = (Hm x : ℂ) := fun x =>
      congrArg Subtype.val (congr_fun hFlift x)
    set θ : ℝ → ℝ := fun u => (F (0, u)).im with hθdef
    have hθc : Continuous θ := by
      rw [hθdef]
      exact Complex.continuous_im.comp (F.continuous.comp
        (Continuous.prodMk continuous_const continuous_id))
    have hFexp : ∀ u, Complex.exp (F (0,u)) = c u := by
      intro u
      rw [hFlift', hHmval, hcdef, Pp_fst_zero]
    -- drift zero
    have hG00 : G (0,0) = (p : ℂ) := by rw [hGdef]; simp [hg0]
    have hG11 : G (1,1) = (p : ℂ) := by rw [hGdef]; simp [hg1]
    have hWmem : ∀ s, F (s,1) - F (s,0) ∈ AddSubgroup.zmultiples ((2*Real.pi : ℂ) * Complex.I) := by
      intro s
      rw [AddSubgroup.mem_zmultiples_iff]
      have h1 : Complex.exp (F (s,1)) = (p : ℂ) := by
        rw [hFlift', hHmval]
        rw [Pp_snd_one s, hG00]
      have h2 : Complex.exp (F (s,0)) = (p : ℂ) := by
        rw [hFlift', hHmval]
        rw [Pp_snd_zero s, hG11]
      have h3 : Complex.exp (F (s,1) - F (s,0)) = 1 := by
        rw [Complex.exp_sub, h1, h2, div_self]
        exact_mod_cast hp.ne'
      obtain ⟨n, hn⟩ := Complex.exp_eq_one_iff.mp h3
      exact ⟨n, by rw [zsmul_eq_mul]; exact hn.symm⟩
    have hWconst : ∀ s, F (s,1) - F (s,0) = F (0,1) - F (0,0) := by
      have hcont : Continuous (fun s : ℝ => F (s,1) - F (s,0)) := by
        exact (F.continuous.comp (Continuous.prodMk continuous_id continuous_const)).sub
          (F.continuous.comp (Continuous.prodMk continuous_id continuous_const))
      exact const_of_mem_zmultiples hcont hWmem
    have hW1 : F (1,1) - F (1,0) = 0 := by
      have hVmem : ∀ u, F (1,u) - F (1,0) ∈ AddSubgroup.zmultiples ((2*Real.pi : ℂ) * Complex.I) := by
        intro u
        rw [AddSubgroup.mem_zmultiples_iff]
        have h2 : Complex.exp (F (1,0)) = (p : ℂ) := by
          rw [hFlift', hHmval]
          rw [Pp_snd_zero (1:ℝ), hG11]
        have h3 : Complex.exp (F (1,u)) = (p : ℂ) := by
          rw [hFlift', hHmval, Pp_fst_one]
          simp only [hGdef, dd]
          ring
        have h4 : Complex.exp (F (1,u) - F (1,0)) = 1 := by
          rw [Complex.exp_sub, h3, h2, div_self]
          exact_mod_cast hp.ne'
        obtain ⟨n, hn⟩ := Complex.exp_eq_one_iff.mp h4
        exact ⟨n, by rw [zsmul_eq_mul]; exact hn.symm⟩
      have hcont : Continuous (fun u : ℝ => F (1,u) - F (1,0)) := by
        exact (F.continuous.comp (Continuous.prodMk continuous_const continuous_id)).sub continuous_const
      have := const_of_mem_zmultiples hcont hVmem 1
      rw [this]; simp
    have hdrift0 : θ 1 - θ 0 = 0 := by
      rw [hθdef]
      have hw := hWconst 1
      rw [hW1] at hw
      have hwim := congrArg Complex.im hw
      simp only [Complex.sub_im, Complex.zero_im] at hwim
      linarith [hwim]
    -- oddness
    have hmem : ∀ u ∈ Set.Icc (0:ℝ) (1/2),
        θ (u+1/2) - θ u - Real.pi ∈ AddSubgroup.zmultiples (2*Real.pi) := by
      intro u hu
      have hexp1 : Complex.exp (F (0, u+1/2)) = c (u+1/2) := hFexp _
      have hexp2 : Complex.exp (F (0, u)) = c u := hFexp _
      have hrel' : c (u+1/2) = - c u := hrel u hu
      have h1 : Complex.exp (F (0,u+1/2)) = - Complex.exp (F (0,u)) := by
        rw [hexp1, hrel', ← hexp2]
      have h2 : Complex.exp (F (0,u+1/2) - F (0,u) - (Real.pi:ℂ)*Complex.I) = 1 := by
        have harg : F (0,u+1/2) - F (0,u) - (Real.pi:ℂ)*Complex.I
            = F (0,u+1/2) - (F (0,u) + (Real.pi:ℂ)*Complex.I) := by ring
        rw [harg, Complex.exp_sub, Complex.exp_add, Complex.exp_pi_mul_I, mul_neg_one, h1]
        exact div_self (neg_ne_zero.mpr (Complex.exp_ne_zero _))
      obtain ⟨n, hn⟩ := Complex.exp_eq_one_iff.mp h2
      rw [AddSubgroup.mem_zmultiples_iff]
      refine ⟨n, ?_⟩
      have htake : (F (0,u+1/2) - F (0,u) - (Real.pi:ℂ)*Complex.I).im
          = θ (u+1/2) - θ u - Real.pi := by
        rw [hθdef]; simp [Complex.sub_im, Complex.mul_I_im]
      have him : (↑n * (2*↑Real.pi*Complex.I) : ℂ).im = (n:ℝ) * (2*Real.pi) := by
        simp [Complex.mul_im]
      rw [hn] at htake
      rw [him] at htake
      rw [zsmul_eq_mul]
      exact htake
    -- final contradiction
    have hhalf : θ (1/2) - θ 0 - Real.pi = θ 1 - θ (1/2) - Real.pi := by
      have h02 : (0:ℝ) ≤ 1/2 := by norm_num
      set s1 : ℝ → ℝ := fun u => (Set.projIcc 0 (1/2) h02 u : ℝ) with hs1def
      have hs1mem : ∀ u, s1 u ∈ Set.Icc (0:ℝ) (1/2) := fun u => (Set.projIcc 0 (1/2) h02 u).2
      have hs1cont : Continuous s1 := continuous_subtype_val.comp continuous_projIcc
      have hs10 : s1 0 = 0 := by simp [hs1def, Set.coe_projIcc]
      have hs1half : s1 (1/2) = 1/2 := by simp [hs1def, Set.coe_projIcc]
      set Φ : ℝ → ↥(AddSubgroup.zmultiples (2*Real.pi)) :=
        fun u => ⟨θ (s1 u + 1/2) - θ (s1 u) - Real.pi, hmem (s1 u) (hs1mem u)⟩ with hΦdef
      have hΦcont : Continuous Φ := Continuous.subtype_mk
        (((hθc.comp (hs1cont.add continuous_const)).sub (hθc.comp hs1cont)).sub continuous_const) _
      have hkey : Φ 0 = Φ (1/2) := PreconnectedSpace.constant (α := ℝ)
        (Y := ↥(AddSubgroup.zmultiples (2*Real.pi))) (inferInstance : PreconnectedSpace ℝ) hΦcont
      have hval := congrArg Subtype.val hkey
      simp only [hΦdef] at hval
      rw [hs10, hs1half] at hval
      have h1 : (0:ℝ) + 1/2 = 1/2 := by norm_num
      have h2 : (1:ℝ)/2 + 1/2 = 1 := by norm_num
      rw [h1, h2] at hval
      exact hval
    obtain ⟨m, hm⟩ := AddSubgroup.mem_zmultiples_iff.mp (hmem 0 (by norm_num))
    have hm' : θ (1/2) - θ 0 - Real.pi = (m:ℝ)*(2*Real.pi) := by
      simpa [zsmul_eq_mul] using hm.symm
    have hm2 : θ 1 - θ (1/2) - Real.pi = (m:ℝ)*(2*Real.pi) := by rw [← hhalf]; exact hm'
    have hcontra : θ 1 - θ 0 = 2*Real.pi*(1 + 2*(m:ℝ)) := by linarith [hm', hm2]
    rw [hdrift0] at hcontra
    have hzero2 : (2*Real.pi)*(1 + 2*(m:ℝ)) = 0 := by linarith [hcontra]
    have h2pi : (2*Real.pi) ≠ 0 := by positivity
    have hone : (1 + 2*(m:ℝ)) = 0 := (mul_eq_zero.mp hzero2).resolve_left h2pi
    have hZ : (1 + 2*m : ℤ) = 0 := by exact_mod_cast hone
    omega

end PathShift

/-- **`path_shift_meets`.** A continuous path `γ` in the plane from `z` to `z + (2p,0)`
(`p > 0`) meets its own translate by `(p,0)`: there are `s, t` with
`γ s = ((γ t).1 - p, (γ t).2)`. -/
theorem path_shift_meets {p a b : ℝ} (hp : 0 < p) (hab : a < b)
    {U : Set (ℝ × ℝ)} (hUsub : U ⊆ {q : ℝ × ℝ | a < q.2 ∧ q.2 < b}) (hUopen : IsOpen U)
    (hUinv : ∀ q : ℝ × ℝ, q ∈ U ↔ (q.1 + 2 * p, q.2) ∈ U)
    {z : ℝ × ℝ} (hz : z ∈ U)
    (γ : C(Set.Icc (0:ℝ) 1, ℝ × ℝ)) (hγ0 : γ 0 = z) (hγ1 : γ 1 = (z.1 + 2 * p, z.2))
    (hγU : ∀ t, γ t ∈ U) :
    ∃ s t : Set.Icc (0:ℝ) 1, γ s = ((γ t).1 - p, (γ t).2) := by
  exact PathShift.path_shift_meets_planar p hp γ (by rw [hγ1, hγ0])

end

end Commons.Topology.Strip