import Mathlib
import Submission.Work.Drive.N2.roundConfigDefs
import Submission.Work.Drive.N2.roundConfigPicture
import Submission.Work.Drive.Morse

namespace Work.Drive.N2

open scoped Manifold ContDiff Topology

theorem roundConfigPictureGlobal {M : Type*} [TopologicalSpace M]
    [ChartedSpace (EuclideanSpace ℝ (Fin 2)) M] [IsManifold (𝓡 2) ∞ M]
    [T2Space M] [SecondCountableTopology M] [CompactSpace M]
    {f : M → ℝ} {b : ℝ} {n : ℕ} (γ : Fin n → ℝ → M)
    (hf : ContMDiff (𝓡 2) 𝓘(ℝ, ℝ) ((⊤ : ℕ∞) : WithTop ℕ∞) f)
    (hreg : ∀ x : M, f x = b → ¬ Work.Drive.Morse.IsCritical f x)
    (hγsm : ∀ i, ContMDiff 𝓘(ℝ, ℝ) (𝓡 2) ((⊤ : ℕ∞) : WithTop ℕ∞) (γ i))
    (hγval : ∀ (i : Fin n) (x : ℝ), f (γ i x) = b)
    (hγper : ∀ i x, γ i (x + 1) = γ i x)
    (hγinj : ∀ i, Set.InjOn (γ i) (Set.Ico 0 1))
    (hγlev : ∀ x : M, f x = b → ∃ (i : Fin n) (t : ℝ), x = γ i t)
    (hγdisj : ∀ i j : Fin n, i ≠ j → Disjoint (Set.range (γ i)) (Set.range (γ j)))
    (hγker : ∀ (i : Fin n) (x : ℝ) (v : TangentSpace (𝓡 2) (γ i x)),
      mfderiv (𝓡 2) 𝓘(ℝ, ℝ) f (γ i x) v = 0 →
        ∃ t : ℝ, mfderiv 𝓘(ℝ, ℝ) (𝓡 2) (γ i) x t = v)
    {D : ℝ → Work.Drive.N2.RoundConfig n} (hD : ∀ s : ℝ, (D s).Disjoint)
    (hDpos : ∀ i : Fin n, ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun s : ℝ => (D s).pos i))
    (hDrad : ∀ i : Fin n, ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun s : ℝ => (D s).rad i))
    (hDph : ∀ i : Fin n, ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun s : ℝ => (D s).phase i)) :
    ∃ P : ℝ → M → EuclideanSpace ℝ (Fin 3),
      (∀ (s : ℝ) (i : Fin n) (x : ℝ), P s (γ i x) = (D s).circle i x) ∧
      (∀ (s : ℝ) (x y : M), (∃ (i : Fin n) (t : ℝ), x = γ i t) →
        (∃ (j : Fin n) (u : ℝ), y = γ j u) → P s x = P s y → x = y) ∧
      (∀ (s : ℝ) (x : M), (∃ (i : Fin n) (t : ℝ), x = γ i t) →
        ∀ v : TangentSpace (𝓡 2) x, mfderiv (𝓡 2) 𝓘(ℝ, ℝ) f x v = 0 →
          mfderiv (𝓡 2) (𝓡 3) (P s) x v = 0 → v = 0) ∧
      ContMDiff ((𝓘(ℝ, ℝ)).prod (𝓡 2)) (𝓡 3) ((⊤ : ℕ∞) : WithTop ℕ∞)
        (fun p : ℝ × M => P p.1 p.2) := by
  classical
  -- Same construction as `Work.Drive.N2.roundConfigPicture`, but the joint smoothness of
  -- `(s, x) ↦ P s x` is *global* here rather than only at the points `x` of the level set
  -- `f ⁻¹' {b}`: the picture `P s x = ∑ i, χ i x • (circle datum i s evaluated at x)` is
  -- smooth on `ℝ × M` because the `χ i` and the extensions `Va i`, `Vb i` are globally smooth
  -- and `pos, rad, phase` are smooth functions of `s` (`hDpos`, `hDrad`, `hDph`).
  haveI hLV : LevelHyp f b := ⟨hf, hreg⟩
  -- each curve is an immersion at every parameter
  have himm : ∀ (i : Fin n) (t : ℝ), mfderiv 𝓘(ℝ,ℝ) (𝓡 2) (γ i) t 1 ≠ 0 := by
    intro i t h1
    obtain ⟨v, hvne, hv0⟩ :=
      exists_ne_zero_ker (mfderiv (𝓡 2) 𝓘(ℝ,ℝ) f (γ i t))
    obtain ⟨s, hs⟩ := hγker i t v hv0
    have hsa : s • (1 : TangentSpace 𝓘(ℝ,ℝ) t) = s := by
      show s * 1 = s
      ring
    have hs0 : (mfderiv 𝓘(ℝ,ℝ) (𝓡 2) (γ i) t) s = 0 := by
      conv_lhs => rw [← hsa, ContinuousLinearMap.map_smul]
      rw [h1, smul_zero]
    rw [hs] at hs0
    exact hvne hs0
  -- the two angle functions extend smoothly along each curve
  have hext : ∀ i : Fin n, ∃ (Va Vb : M → EuclideanSpace ℝ (Fin 3)),
      ContMDiff (𝓡 2) (𝓘(ℝ,EuclideanSpace ℝ (Fin 3))) ∞ Va ∧ (∀ t, Va (γ i t) = ang t) ∧
      ContMDiff (𝓡 2) (𝓘(ℝ,EuclideanSpace ℝ (Fin 3))) ∞ Vb ∧
        (∀ t, Vb (γ i t) = angPerp t) := by
    intro i
    obtain ⟨Va, h1, h2⟩ := exists_contMDiff_extend_of_circle (f := f) (b := b) (γ i) (hγsm i)
      (hγval i) (hγper i) (hγinj i) (himm i) ang ang_contDiff ang_periodic
    obtain ⟨Vb, h3, h4⟩ := exists_contMDiff_extend_of_circle (f := f) (b := b) (γ i) (hγsm i)
      (hγval i) (hγper i) (hγinj i) (himm i) angPerp angPerp_contDiff angPerp_periodic
    exact ⟨Va, Vb, h1, h2, h3, h4⟩
  choose Va Vb hVa_sm hVa_val hVb_sm hVb_val using hext
  -- a bump which is `1` on the `i`-th circle and `0` on all the others
  have hbump : ∀ i : Fin n, ∃ χ : M → ℝ, ContMDiff (𝓡 2) 𝓘(ℝ,ℝ) ∞ χ ∧
      (∀ t, χ (γ i t) = 1) ∧ (∀ j, j ≠ i → ∀ t, χ (γ j t) = 0) := by
    intro i
    have hKi : IsCompact (Set.range (γ i)) := by
      rw [range_periodic (hγper i)]
      exact isCompact_Icc.image (hγsm i).continuous
    have hKo : IsCompact (⋃ j : {j : Fin n // j ≠ i}, Set.range (γ j.1)) := by
      refine isCompact_iUnion fun j => ?_
      rw [range_periodic (hγper j.1)]
      exact isCompact_Icc.image (hγsm j.1).continuous
    have hdisj : Disjoint (Set.range (γ i))
        (⋃ j : {j : Fin n // j ≠ i}, Set.range (γ j.1)) := by
      rw [Set.disjoint_iUnion_right]
      intro j
      exact hγdisj i j.1 (Ne.symm j.2)
    obtain ⟨U, W, hUo, hWo, hKU, hKW, hUW⟩ :=
      SeparatedNhds.of_isCompact_isCompact hKi hKo hdisj
    obtain ⟨χ, V, hχsm, hχsupp, hVopen, hKV, hχone, _⟩ :=
      exists_contMDiff_bump_tsupport hKi hUo hKU
    refine ⟨χ, hχsm, ?_, ?_⟩
    · intro t
      exact hχone _ (hKV ⟨t, rfl⟩)
    · intro j hj t
      by_contra hne
      have h1 : γ j t ∈ Function.support χ := by rwa [Function.mem_support]
      have h3 : γ j t ∈ U := hχsupp (subset_closure h1)
      have h4 : γ j t ∈ W := hKW (Set.mem_iUnion.mpr ⟨⟨j, hj⟩, ⟨t, rfl⟩⟩)
      exact Set.disjoint_left.mp hUW h3 h4
  choose χ hχsm hχone hχzero using hbump
  -- the picture
  let P : ℝ → M → EuclideanSpace ℝ (Fin 3) := fun s x => ∑ i : Fin n,
      χ i x • ((D s).pos i + (D s).rad i • (Real.cos ((D s).phase i) • Va i x
        + Real.sin ((D s).phase i) • Vb i x))
  have hP1 : ∀ (s : ℝ) (i : Fin n) (t : ℝ), P s (γ i t) = (D s).circle i t := by
    intro s i t
    show (∑ j : Fin n, χ j (γ i t) • ((D s).pos j + (D s).rad j •
        (Real.cos ((D s).phase j) • Va j (γ i t)
          + Real.sin ((D s).phase j) • Vb j (γ i t)))) = (D s).circle i t
    rw [Finset.sum_eq_single i]
    · rw [hχone i t, one_smul, hVa_val i t, hVb_val i t]
      exact (circle_eq_ang_combo (D s) i t).symm
    · intro j _ hj
      rw [hχzero j i (Ne.symm hj) t, zero_smul]
    · intro hmem
      exact absurd (Finset.mem_univ i) hmem
  have hPsm : ∀ s : ℝ, ContMDiff (𝓡 2) (𝓡 3) ∞ (P s) := by
    intro s
    rw [show P s = fun x : M => ∑ i : Fin n, χ i x •
        ((D s).pos i + (D s).rad i • (Real.cos ((D s).phase i) • Va i x
          + Real.sin ((D s).phase i) • Vb i x)) from rfl]
    refine ContMDiff.sum fun i _ => ?_
    have hpos : ContMDiff (𝓡 2) (𝓡 3) ∞ (fun _ : M => (D s).pos i) := contMDiff_const
    have hrad : ContMDiff (𝓡 2) 𝓘(ℝ,ℝ) ∞ (fun _ : M => (D s).rad i) := contMDiff_const
    have hcos : ContMDiff (𝓡 2) 𝓘(ℝ,ℝ) ∞ (fun _ : M => Real.cos ((D s).phase i)) :=
      Real.contDiff_cos.contMDiff.comp contMDiff_const
    have hsin : ContMDiff (𝓡 2) 𝓘(ℝ,ℝ) ∞ (fun _ : M => Real.sin ((D s).phase i)) :=
      Real.contDiff_sin.contMDiff.comp contMDiff_const
    exact (hχsm i).smul (hpos.add (hrad.smul ((hcos.smul (hVa_sm i)).add
      (hsin.smul (hVb_sm i)))))
  have hPsm2 : ContMDiff ((𝓘(ℝ,ℝ)).prod (𝓡 2)) (𝓡 3) ∞ (fun p : ℝ × M => P p.1 p.2) := by
    rw [show (fun p : ℝ × M => P p.1 p.2) = fun p : ℝ × M => ∑ i : Fin n, χ i p.2 •
        ((D p.1).pos i + (D p.1).rad i • (Real.cos ((D p.1).phase i) • Va i p.2
          + Real.sin ((D p.1).phase i) • Vb i p.2)) from rfl]
    refine ContMDiff.sum fun i _ => ?_
    have hχi : ContMDiff ((𝓘(ℝ,ℝ)).prod (𝓡 2)) 𝓘(ℝ,ℝ) ∞ (fun p : ℝ × M => χ i p.2) :=
      (hχsm i).comp contMDiff_snd
    have hpos : ContMDiff ((𝓘(ℝ,ℝ)).prod (𝓡 2)) (𝓡 3) ∞ (fun p : ℝ × M => (D p.1).pos i) :=
      (contMDiff_iff_contDiff.mpr (hDpos i)).comp contMDiff_fst
    have hrad : ContMDiff ((𝓘(ℝ,ℝ)).prod (𝓡 2)) 𝓘(ℝ,ℝ) ∞ (fun p : ℝ × M => (D p.1).rad i) :=
      (contMDiff_iff_contDiff.mpr (hDrad i)).comp contMDiff_fst
    have hph : ContMDiff ((𝓘(ℝ,ℝ)).prod (𝓡 2)) 𝓘(ℝ,ℝ) ∞ (fun p : ℝ × M => (D p.1).phase i) :=
      (contMDiff_iff_contDiff.mpr (hDph i)).comp contMDiff_fst
    have hcos : ContMDiff ((𝓘(ℝ,ℝ)).prod (𝓡 2)) 𝓘(ℝ,ℝ) ∞
        (fun p : ℝ × M => Real.cos ((D p.1).phase i)) :=
      Real.contDiff_cos.contMDiff.comp hph
    have hsin : ContMDiff ((𝓘(ℝ,ℝ)).prod (𝓡 2)) 𝓘(ℝ,ℝ) ∞
        (fun p : ℝ × M => Real.sin ((D p.1).phase i)) :=
      Real.contDiff_sin.contMDiff.comp hph
    have hVai : ContMDiff ((𝓘(ℝ,ℝ)).prod (𝓡 2)) (𝓡 3) ∞ (fun p : ℝ × M => Va i p.2) :=
      (hVa_sm i).comp contMDiff_snd
    have hVbi : ContMDiff ((𝓘(ℝ,ℝ)).prod (𝓡 2)) (𝓡 3) ∞ (fun p : ℝ × M => Vb i p.2) :=
      (hVb_sm i).comp contMDiff_snd
    exact hχi.smul (hpos.add (hrad.smul ((hcos.smul hVai).add (hsin.smul hVbi))))
  refine ⟨P, hP1, ?_, ?_, ?_⟩
  · -- injectivity on the level set
    intro s x y hx hy hxy
    obtain ⟨i, t, rfl⟩ := hx
    obtain ⟨j, u, rfl⟩ := hy
    rw [hP1 s i t, hP1 s j u] at hxy
    by_cases hij : i = j
    · subst hij
      obtain ⟨k, hk⟩ := circle_eq_mod_one (D s) i hxy
      have hku : u = t + ((-k : ℤ) : ℝ) := by push_cast; linarith [hk]
      rw [hku]
      exact (periodic_int (hγper i) (-k) t).symm
    · exact absurd hxy (hD s i j hij t u)
  · -- immersion on the level set
    intro s x hx v hv h0
    obtain ⟨i, t, rfl⟩ := hx
    obtain ⟨t', ht'⟩ := hγker i t v hv
    have hPdiff : MDifferentiableAt (𝓡 2) (𝓡 3) (P s) (γ i t) :=
      (hPsm s).contMDiffAt.mdifferentiableAt (by simp)
    have hγdiff : MDifferentiableAt 𝓘(ℝ,ℝ) (𝓡 2) (γ i) t :=
      (hγsm i).contMDiffAt.mdifferentiableAt (by simp)
    have hfun : ((P s) ∘ (γ i)) = fun u : ℝ => (D s).circle i u := by
      funext u
      exact hP1 s i u
    have hcomp : mfderiv 𝓘(ℝ,ℝ) (𝓡 3) ((P s) ∘ (γ i)) t t'
        = mfderiv (𝓡 2) (𝓡 3) (P s) (γ i t)
            (mfderiv 𝓘(ℝ,ℝ) (𝓡 2) (γ i) t t') := by
      rw [mfderiv_comp (x := t) (f := γ i) (g := P s) hPdiff hγdiff]
      rfl
    have hcirc : mfderiv 𝓘(ℝ,ℝ) (𝓡 3) (fun u : ℝ => (D s).circle i u) t t' = 0 := by
      have h1 : mfderiv (𝓡 2) (𝓡 3) (P s) (γ i t) v = 0 := h0
      rw [← ht'] at h1
      rw [← hcomp, hfun] at h1
      exact h1
    have hne : (mfderiv 𝓘(ℝ,ℝ) (𝓡 3) (fun u : ℝ => (D s).circle i u) t) 1 ≠ 0 := by
      intro hzero
      have h1 : (mfderiv 𝓘(ℝ,ℝ) (𝓡 3) (fun u : ℝ => (D s).circle i u) t :
          ℝ →L[ℝ] EuclideanSpace ℝ (Fin 3)) 1 = 0 := hzero
      rw [mfderiv_eq_fderiv] at h1
      exact circle_deriv_ne_zero (D s) i t h1
    have hta : t' • (1 : TangentSpace 𝓘(ℝ,ℝ) t) = t' := by
      show t' * 1 = t'
      ring
    have hsmul : t' • ((mfderiv 𝓘(ℝ,ℝ) (𝓡 3) (fun u : ℝ => (D s).circle i u) t) 1) = 0 := by
      conv_lhs => rw [← ContinuousLinearMap.map_smul, hta]
      rw [hcirc]
    have hzero : t' = 0 := by
      rcases smul_eq_zero.mp hsmul with h' | h'
      · exact h'
      · exact absurd h' hne
    have hv0 : v = 0 := by
      have hlin : (mfderiv 𝓘(ℝ,ℝ) (𝓡 2) (γ i) t) t'
          = t' • ((mfderiv 𝓘(ℝ,ℝ) (𝓡 2) (γ i) t) 1) := by
        have hta2 : t' • (1 : TangentSpace 𝓘(ℝ,ℝ) t) = t' := by
          show t' * 1 = t'
          ring
        conv_lhs => rw [← hta2, ContinuousLinearMap.map_smul]
      rw [hlin, hzero, zero_smul] at ht'
      exact ht'.symm
    exact hv0
  · -- global joint smoothness (the same construction, used whole)
    exact hPsm2


end Work.Drive.N2
