import Mathlib.Analysis.CStarAlgebra.Classes
import Mathlib.Analysis.Meromorphic.Order
import Submission.Commons.NumberTheory.Zeta.logDeriv_sub_pole_analyticAt

namespace Commons.Analysis.MeromorphicOn

open Filter
open scoped Topology

/-- If `f =ᶠ[𝓝 ρ] (· - ρ)^n * g` with `g` analytic and nonvanishing at `ρ`, then
`logDeriv f` agrees on the punctured neighbourhood with `n/(·-ρ) + logDeriv g`. -/
lemma logDeriv_eq_nat_div_sub_add {f g : ℂ → ℂ} {ρ : ℂ} {n : ℕ}
    (hg : AnalyticAt ℂ g ρ) (hgρ : g ρ ≠ 0)
    (hfac : f =ᶠ[𝓝 ρ] fun z => (z - ρ) ^ n * g z) :
    logDeriv f =ᶠ[𝓝[≠] ρ] fun z => (n : ℂ) / (z - ρ) + logDeriv g z := by
  have hld_aff : ∀ s : ℂ, s ≠ ρ → logDeriv (fun s : ℂ => s - ρ) s = 1 / (s - ρ) := by
    intro s _
    unfold logDeriv
    have hd : deriv (fun s : ℂ => s - ρ) s = 1 := by
      simpa using ((hasDerivAt_id s).sub_const ρ).deriv
    change (deriv (fun s : ℂ => s - ρ) s) / (s - ρ) = 1 / (s - ρ)
    rw [hd]
  have h1 : logDeriv f =ᶠ[𝓝[≠] ρ] logDeriv (fun z => (z - ρ) ^ n * g z) :=
    logDeriv_congr_nhdsNE (hfac.filter_mono nhdsWithin_le_nhds)
  filter_upwards [h1, hg.eventually_analyticAt.filter_mono nhdsWithin_le_nhds,
      (hg.continuousAt.eventually_ne hgρ).filter_mono nhdsWithin_le_nhds,
      eventually_mem_nhdsWithin] with z hz hgan hgne hzmem
  have hzρ : z ≠ ρ := by simpa using hzmem
  rw [hz]
  rw [show (fun z => (z - ρ) ^ n * g z) = (fun w : ℂ => (w - ρ) ^ n) * g from rfl]
  rw [logDeriv_mul (f := fun w : ℂ => (w - ρ) ^ n) (g := g) z
    (pow_ne_zero n (sub_ne_zero.mpr hzρ)) hgne (by fun_prop) hgan.differentiableAt]
  rw [logDeriv_fun_pow (by fun_prop : DifferentiableAt ℂ (fun w : ℂ => w - ρ) z) n,
    hld_aff z hzρ]
  ring

theorem meromorphicOrderAt_eq_of_logDeriv_sub_pole {f : ℂ → ℂ} {ρ : ℂ} {m : ℕ}
    (hf : AnalyticAt ℂ f ρ) (hρ : f ρ = 0)
    (hnot : ¬(∀ᶠ z in nhds ρ, f z = 0)) (hm : 1 ≤ m)
    (hF : ∃ F : ℂ → ℂ, AnalyticAt ℂ F ρ ∧
      ∀ᶠ s in nhdsWithin ρ {ρ}ᶜ, F s = logDeriv f s - m / (s - ρ)) :
    meromorphicOrderAt f ρ = (m : ℤ) := by
  obtain ⟨F, hF_an, hF_eq⟩ := hF
  have hn_top : analyticOrderAt f ρ ≠ ⊤ := fun h => hnot (analyticOrderAt_eq_top.mp h)
  obtain ⟨n, hn_eq⟩ := ENat.ne_top_iff_exists.mp hn_top
  -- hn_eq : ↑n = analyticOrderAt f ρ
  obtain ⟨g, hg_an, hgρ, hfg⟩ :=
    (hf.analyticOrderAt_eq_natCast (n := n)).mp hn_eq.symm
  have hfac : f =ᶠ[𝓝 ρ] fun z => (z - ρ) ^ n * g z := by
    filter_upwards [hfg] with z hz
    rw [hz, smul_eq_mul]
  have hld := logDeriv_eq_nat_div_sub_add hg_an hgρ hfac
  have hn_eq_m : n = m := by
    by_contra hne
    have hF' : (fun s => F s) =ᶠ[𝓝[≠] ρ]
        (fun s => logDeriv f s - (m : ℂ) / (s - ρ)) := hF_eq
    have hmain : (fun s => F s - logDeriv g s) =ᶠ[𝓝[≠] ρ]
        (fun s => ((n : ℂ) - (m : ℂ)) / (s - ρ)) := by
      filter_upwards [hF', hld, eventually_mem_nhdsWithin] with s hFs hlds hs
      have hsne : s - ρ ≠ 0 := sub_ne_zero.mpr (by simpa using hs)
      rw [hFs, hlds]
      field_simp
      ring
    have hL : 0 ≤ meromorphicOrderAt (fun s => F s - logDeriv g s) ρ :=
      (hF_an.sub (hg_an.deriv.div hg_an hgρ)).meromorphicOrderAt_nonneg
    have hR : meromorphicOrderAt (fun s => ((n : ℂ) - (m : ℂ)) / (s - ρ)) ρ = -1 := by
      have hc : (n : ℂ) - (m : ℂ) ≠ 0 := by
        intro h
        exact hne (by exact_mod_cast sub_eq_zero.mp h : n = m)
      change meromorphicOrderAt ((fun _ : ℂ => ((n : ℂ) - (m : ℂ))) / (fun s : ℂ => s - ρ)) ρ = -1
      rw [meromorphicOrderAt_div (f := fun _ : ℂ => ((n : ℂ) - (m : ℂ)))
        (g := fun s : ℂ => s - ρ) (MeromorphicAt.const _ _)
        ((MeromorphicAt.id ρ).sub (MeromorphicAt.const ρ ρ))]
      have h1 : meromorphicOrderAt (fun _ : ℂ => ((n : ℂ) - (m : ℂ))) ρ = (0 : WithTop ℤ) := by
        rw [meromorphicOrderAt_const]
        simp [hc]
      have h2 : meromorphicOrderAt (fun s : ℂ => s - ρ) ρ = 1 := meromorphicOrderAt_id_sub_const
      rw [h1, h2]
      norm_num
    have hcong := meromorphicOrderAt_congr hmain
    rw [hR] at hcong
    rw [hcong] at hL
    have h' : (0 : ℤ) ≤ -1 := WithTop.coe_le_coe.mp hL
    omega
  have hres : meromorphicOrderAt f ρ = (n : ℤ) := by
    rw [hf.meromorphicOrderAt_eq, ← hn_eq]
    rfl
  rw [hres]
  exact_mod_cast hn_eq_m

end Commons.Analysis.MeromorphicOn