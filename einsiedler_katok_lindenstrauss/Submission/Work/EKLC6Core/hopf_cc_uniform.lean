import Mathlib
import Submission.Work.EKLC6Core.Basic
import Submission.Work.EKLContract.Lemmas.V_open_one
import Submission.Work.EKLProd.sl3EntryBox_compact

/-!
# `Work.EKLC6Core.hopf_cc_uniform` — uniform continuity of the `SL₃(ℝ)`-action on `X₃`

For a continuous compactly supported `f : X₃ → ℝ`, translation `x ↦ v • x` by `v` close to the
identity moves `f` by at most `ε`, *uniformly in* `x`.

`X₃` is not compact, but it only fails to be compact "far away", where `f` vanishes.  Fix a compact
`C ⊆ SL₃(ℝ)` containing a neighbourhood `V 1` of the identity (here an entrywise box).  Then

`K₂ = {v⁻¹ • y : v ∈ C, y ∈ tsupport f}`

is compact, and for `v ∈ C` and `x ∉ K₂` one has `f x = 0` as well as `f (v • x) = 0`, because
otherwise `x = v⁻¹ • (v • x) ∈ K₂`.  So only `x ∈ K₂` matters, and there one argues with the
compactness of the *closed* "bad" set `{(v,x) : v ∈ C, x ∈ K₂, ε ≤ |f (v • x) - f x|}`: its
projection to the first coordinate is compact, is closed (as `SL₃(ℝ)` is Hausdorff) and does not
contain `1`.
-/

open Work.EKLContract

namespace Work.EKLC6Core

theorem hopf_cc_uniform {f : Work.EKLContract.X3 → ℝ} (hf : Continuous f)
    (hs : HasCompactSupport f) :
    ∀ ε > 0, ∃ W : Set Work.EKLContract.SL3, IsOpen W ∧ (1 : Work.EKLContract.SL3) ∈ W ∧
      ∀ v ∈ W, ∀ x : Work.EKLContract.X3, |f (v • x) - f x| ≤ ε := by
  classical
  intro ε hε
  -- the (compact) support of `f`
  let K : Set X3 := tsupport f
  have hKc : IsCompact K := hs.isCompact
  -- a compact entrywise box of matrices containing a neighbourhood of `1`
  let C : Set SL3 := {g : SL3 | ∀ i j, (-2 : ℝ) ≤ g i j ∧ g i j ≤ (2 : ℝ)}
  have hCc : IsCompact C :=
    Work.EKLProd.sl3EntryBox_compact (fun _ _ => (-2 : ℝ)) (fun _ _ => (2 : ℝ))
  have h1C : (1 : SL3) ∈ C := by
    intro i j
    have h : (1 : SL3) i j = (1 : Matrix (Fin 3) (Fin 3) ℝ) i j := rfl
    rw [h, Matrix.one_apply]
    split <;> norm_num
  have hUC : V 1 ⊆ C := by
    intro g hg i j
    have h1 : |(1 : Matrix (Fin 3) (Fin 3) ℝ) i j| ≤ (1 : ℝ) := by
      rw [Matrix.one_apply]
      split <;> norm_num
    have h2 : |g i j - (1 : Matrix (Fin 3) (Fin 3) ℝ) i j| < 1 := hg i j
    have h3 : |g i j| ≤ |g i j - (1 : Matrix (Fin 3) (Fin 3) ℝ) i j|
        + |(1 : Matrix (Fin 3) (Fin 3) ℝ) i j| := by
      calc |g i j| = |(g i j - (1 : Matrix (Fin 3) (Fin 3) ℝ) i j)
            + (1 : Matrix (Fin 3) (Fin 3) ℝ) i j| := by
            congr 1; ring
        _ ≤ |g i j - (1 : Matrix (Fin 3) (Fin 3) ℝ) i j|
            + |(1 : Matrix (Fin 3) (Fin 3) ℝ) i j| := abs_add_le _ _
    have h4 : |g i j| ≤ 2 := by linarith
    exact abs_le.mp h4
  -- the compact set to which the whole problem is confined
  let K₂ : Set X3 := (fun p : SL3 × X3 => p.1⁻¹ • p.2) '' (C ×ˢ K)
  have hK₂c : IsCompact K₂ :=
    (hCc.prod hKc).image ((continuous_fst.inv).smul continuous_snd)
  have hKsub : K ⊆ K₂ := by
    intro x hx
    exact ⟨(1, x), ⟨h1C, hx⟩, by simp⟩
  have hkey : ∀ v ∈ V 1, ∀ x : X3, v • x ∈ K → x ∈ K₂ := by
    intro v hv x hx
    refine ⟨(v, v • x), ⟨hUC hv, hx⟩, ?_⟩
    show v⁻¹ • (v • x) = x
    rw [inv_smul_smul]
  -- the closed "bad" set, confined to the compact `C ×ˢ K₂`
  have hcont : Continuous (fun p : SL3 × X3 => |f (p.1 • p.2) - f p.2|) :=
    ((hf.comp continuous_smul).sub (hf.comp continuous_snd)).abs
  have hBclosed : IsClosed {p : SL3 × X3 | ε ≤ |f (p.1 • p.2) - f p.2|} :=
    isClosed_le continuous_const hcont
  have hBc : IsCompact ({p : SL3 × X3 | ε ≤ |f (p.1 • p.2) - f p.2|} ∩ (C ×ˢ K₂)) :=
    (hCc.prod hK₂c).inter_left hBclosed
  let pr : Set SL3 := Prod.fst '' ({p : SL3 × X3 | ε ≤ |f (p.1 • p.2) - f p.2|} ∩ (C ×ˢ K₂))
  have hprc : IsCompact pr := hBc.image continuous_fst
  have h1pr : (1 : SL3) ∉ pr := by
    rintro ⟨p, hp, hp1⟩
    have hle : ε ≤ |f (p.1 • p.2) - f p.2| := hp.1
    rw [hp1, one_smul, sub_self, abs_zero] at hle
    linarith
  refine ⟨prᶜ ∩ V 1, hprc.isClosed.isOpen_compl.inter
      (Work.EKLContract.Lemmas.V_open_one 1 one_pos).1,
    ⟨h1pr, (Work.EKLContract.Lemmas.V_open_one 1 one_pos).2⟩, ?_⟩
  intro v hv x
  rcases hv with ⟨hv1, hvU⟩
  by_cases hx : x ∈ K₂
  · have hnotB : (v, x) ∉ ({p : SL3 × X3 | ε ≤ |f (p.1 • p.2) - f p.2|} ∩ (C ×ˢ K₂)) := by
      intro hB
      exact (Set.mem_compl_iff pr v).mp hv1 ⟨(v, x), hB, rfl⟩
    have hmem : (v, x) ∈ C ×ˢ K₂ := Set.mem_prod.mpr ⟨hUC hvU, hx⟩
    have hlt : ¬ (ε ≤ |f (v • x) - f x|) := fun hle => hnotB ⟨hle, hmem⟩
    exact le_of_lt (not_le.mp hlt)
  · have hfx : f x = 0 := image_eq_zero_of_notMem_tsupport (fun hmem => hx (hKsub hmem))
    have hfvx : f (v • x) = 0 :=
      image_eq_zero_of_notMem_tsupport (fun hmem => hx (hkey v hvU x hmem))
    rw [hfx, hfvx, sub_self, abs_zero]
    linarith

end Work.EKLC6Core
