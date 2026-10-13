/-
  WilG1 / OneDim — `infDeriv_mem`.

  The set of points where the two-sided difference quotient of `g` tends to `±∞` (in the
  direction `s = ±1`) is `Ω`-definable from the graph of `g`, with format `F + 1000` and
  degree `1000 * (D + 1)`.

  The defining first-order formula

    `{x | ∀ M, 1 < M → ∃ δ, 0 < δ ∧ ∀ y, y ≠ x → |y - x| < δ →
            M < s * (g y - g x) / (y - x)}`

  is coded explicitly.  In the coordinate spaces `ℝ² ⊂ ℝ³ ⊂ … ⊂ ℝ⁷` with coordinates

    `(x, a, M, δ, y, b, t)`   (`a = g x`, `b = g y`, `t` a witness)

  we build, with `G` the graph of `g`:

  * `GX2`  = `{a = g x}` (a substitution atom), `GY6` = `{b = g y}`;
  * `LtM3` = `{1 < M}`, `PosDelta4` = `{0 < δ}`, `PosYDiff5` = `{y ≠ x}`,
    `PosDeltaSq5` = `{|y - x| < δ}`, `C6` = `{0 < s (b - a)(y-x) - M (y-x)^2}`  —
    each obtained as the projection of a hypersurface `t ^ 2 A - 1 = 0`;
  * `A5 = PosYDiff5 ∩ PosDeltaSq5`, `Wire5 = projLast (GY6 ∩ C6)`,
    `Body5 = A5 ∩ Wire5ᶜ`, `Delta4 = PosDelta4 ∩ (projLast Body5)ᶜ`,
    `Inner3 = LtM3 ∩ (projLast Delta4)ᶜ`, `Rest2 = (projLast Inner3)ᶜ`,
    `F2 = GX2 ∩ Rest2`.

  Every projection/complement/intersection costs one axiom of `SOMin`; the format grows by
  the fixed constant `31` and the degree by `2D + 23`, well within `F + 1000` and
  `1000 (D + 1)`.
-/
import Submission.Work.WilG1.OneDim.infDeriv_mem_aux

set_option autoImplicit false
noncomputable section

open Classical
open WilkiesDesign

namespace Work.WilG1.OneDim

theorem infDeriv_mem {S : WilkiesDesign.SOMin} {F D : ℕ} (g : ℝ → ℝ)
    (hg : WilkiesDesign.graphOf (fun x : Fin 1 → ℝ => g (x 0)) ∈ S.Ω F D 2) (s : ℝ) :
    Work.WilG1.liftR (Work.WilG1.infDeriv g s) ∈
      S.Ω (F + 1000) ((Polynomial.C 1000 * (Polynomial.X + Polynomial.C 1)).eval D) 1 := by
  -- The graph, the two substitution atoms, and the nested set expression.
  set G : Set (Fin 2 → ℝ) := WilkiesDesign.graphOf (fun x : Fin 1 → ℝ => g (x 0)) with hGdef
  set GX2 : Set (Fin 2 → ℝ) := {v : Fin 2 → ℝ | v ∘ (id : Fin 2 → Fin 2) ∈ G} with hGX2def
  set GY6 : Set (Fin 6 → ℝ) := {v : Fin 6 → ℝ | v ∘ infιY ∈ G} with hGY6def
  set LtM3 : Set (Fin 3 → ℝ) := projLast {w : Fin 4 → ℝ | MvPolynomial.eval w infP1 = 0}
    with hLtM3def
  set PosDelta4 : Set (Fin 4 → ℝ) :=
    projLast {w : Fin 5 → ℝ | MvPolynomial.eval w infP2 = 0} with hPosDelta4def
  set PosYDiff5 : Set (Fin 5 → ℝ) :=
    projLast {w : Fin 6 → ℝ | MvPolynomial.eval w infP3 = 0} with hPosYDiff5def
  set PosDeltaSq5 : Set (Fin 5 → ℝ) :=
    projLast {w : Fin 6 → ℝ | MvPolynomial.eval w infP4 = 0} with hPosDeltaSq5def
  set A5 : Set (Fin 5 → ℝ) := PosYDiff5 ∩ PosDeltaSq5 with hA5def
  set C6 : Set (Fin 6 → ℝ) :=
    projLast {w : Fin 7 → ℝ | MvPolynomial.eval w (infP5 s) = 0} with hC6def
  set Inner6 : Set (Fin 6 → ℝ) := GY6 ∩ C6 with hInner6def
  set Wire5 : Set (Fin 5 → ℝ) := projLast Inner6 with hWire5def
  set Body5 : Set (Fin 5 → ℝ) := A5 ∩ Wire5ᶜ with hBody5def
  set ForallY4 : Set (Fin 4 → ℝ) := (projLast Body5)ᶜ with hForallY4def
  set Delta4 : Set (Fin 4 → ℝ) := PosDelta4 ∩ ForallY4 with hDelta4def
  set ExDelta3 : Set (Fin 3 → ℝ) := projLast Delta4 with hExDelta3def
  set Inner3 : Set (Fin 3 → ℝ) := LtM3 ∩ ExDelta3ᶜ with hInner3def
  set Rest2 : Set (Fin 2 → ℝ) := (projLast Inner3)ᶜ with hRest2def
  set F2 : Set (Fin 2 → ℝ) := GX2 ∩ Rest2 with hF2def
  -- Membership in `Ω`, format and degree tracked step by step.
  have hGmem : G ∈ S.Ω F D 2 := by rw [hGdef]; exact hg
  have hGX2 : GX2 ∈ S.Ω (F+9) (D+2) 2 := by
    rw [hGX2def]
    exact Work.WilG0.Omega_mono_FD (by omega) le_rfl
      (Work.WilG0.substSet_mem hGmem 2 (id : Fin 2 → Fin 2))
  have hGY6 : GY6 ∈ S.Ω (F+17) (D+2) 6 := by
    rw [hGY6def]
    exact Work.WilG0.Omega_mono_FD (by omega) le_rfl (Work.WilG0.substSet_mem hGmem 6 infιY)
  have hLtM3 : LtM3 ∈ S.Ω 5 3 3 := by
    rw [hLtM3def]
    exact S.proj (Work.WilG0.Omega_mono_D infP1_td (S.hyp 4 infP1))
  have hPosDelta4 : PosDelta4 ∈ S.Ω 6 3 4 := by
    rw [hPosDelta4def]
    exact S.proj (Work.WilG0.Omega_mono_D infP2_td (S.hyp 5 infP2))
  have hPosYDiff5 : PosYDiff5 ∈ S.Ω 7 4 5 := by
    rw [hPosYDiff5def]
    exact S.proj (Work.WilG0.Omega_mono_D infP3_td (S.hyp 6 infP3))
  have hPosDeltaSq5 : PosDeltaSq5 ∈ S.Ω 7 4 5 := by
    rw [hPosDeltaSq5def]
    exact S.proj (Work.WilG0.Omega_mono_D infP4_td (S.hyp 6 infP4))
  have hC6 : C6 ∈ S.Ω 8 5 6 := by
    rw [hC6def]
    exact S.proj (Work.WilG0.Omega_mono_D (infP5_td s) (S.hyp 7 (infP5 s)))
  have hA5 : A5 ∈ S.Ω 8 8 5 := by
    rw [hA5def]
    exact Work.WilG0.Omega_inter2 hPosYDiff5 hPosDeltaSq5
  have hInner6 : Inner6 ∈ S.Ω (F+18) ((D+2)+5) 6 := by
    rw [hInner6def]
    exact Work.WilG0.Omega_inter2 hGY6 (Work.WilG0.Omega_mono_F (by omega) hC6)
  have hWire5 : Wire5 ∈ S.Ω (F+19) ((D+2)+5) 5 := by
    rw [hWire5def]; exact S.proj hInner6
  have hWire5c : Wire5ᶜ ∈ S.Ω (F+20) ((D+2)+5) 5 := S.compl hWire5
  have hBody5 : Body5 ∈ S.Ω (F+21) (8 + ((D+2)+5)) 5 := by
    rw [hBody5def]
    exact Work.WilG0.Omega_inter2 (Work.WilG0.Omega_mono_F (by omega) hA5) hWire5c
  have hForallY4 : ForallY4 ∈ S.Ω (F+23) (8 + ((D+2)+5)) 4 := by
    rw [hForallY4def]; exact S.compl (S.proj hBody5)
  have hDelta4 : Delta4 ∈ S.Ω (F+24) (3 + (8 + ((D+2)+5))) 4 := by
    rw [hDelta4def]
    exact Work.WilG0.Omega_inter2 (Work.WilG0.Omega_mono_F (by omega) hPosDelta4) hForallY4
  have hExDelta3 : ExDelta3 ∈ S.Ω (F+25) (3 + (8 + ((D+2)+5))) 3 := by
    rw [hExDelta3def]; exact S.proj hDelta4
  have hInner3 : Inner3 ∈ S.Ω (F+27) (3 + (3 + (8 + ((D+2)+5)))) 3 := by
    rw [hInner3def]
    exact Work.WilG0.Omega_inter2 (Work.WilG0.Omega_mono_F (by omega) hLtM3)
      (S.compl hExDelta3)
  have hRest2 : Rest2 ∈ S.Ω (F+29) (3 + (3 + (8 + ((D+2)+5)))) 2 := by
    rw [hRest2def]; exact S.compl (S.proj hInner3)
  have hF2 : F2 ∈ S.Ω (F+30) ((D+2) + (3 + (3 + (8 + ((D+2)+5))))) 2 := by
    rw [hF2def]
    exact Work.WilG0.Omega_inter2 (Work.WilG0.Omega_mono_F (by omega) hGX2) hRest2
  have hB : projLast F2 ∈ S.Ω (F+31) ((D+2) + (3 + (3 + (8 + ((D+2)+5))))) 1 := S.proj hF2
  -- Semantic characterisation of each layer.
  have hGX2mem : ∀ v : Fin 2 → ℝ, v ∈ GX2 ↔ v 1 = g (v 0) := by
    intro v; rw [hGX2def]; simp only [Set.mem_ofPred_eq]
    simp [hGdef, WilkiesDesign.graphOf, Function.comp_apply, Fin.init]
  have hGY6mem : ∀ v : Fin 6 → ℝ, v ∈ GY6 ↔ v 5 = g (v 4) := by
    intro v; rw [hGY6def]; simp only [Set.mem_ofPred_eq]
    simp [hGdef, WilkiesDesign.graphOf, Function.comp_apply, infιY, Fin.init]
  have hLtM3mem : ∀ v : Fin 3 → ℝ, v ∈ LtM3 ↔ 1 < v 2 := by
    intro v; rw [hLtM3def]; exact inf_mem_slab1 v
  have hPosDelta4mem : ∀ v : Fin 4 → ℝ, v ∈ PosDelta4 ↔ 0 < v 3 := by
    intro v; rw [hPosDelta4def]; exact inf_mem_slab2 v
  have hPosYDiff5mem : ∀ v : Fin 5 → ℝ, v ∈ PosYDiff5 ↔ 0 < (v 4 - v 0)^2 := by
    intro v; rw [hPosYDiff5def]; exact inf_mem_slab3 v
  have hPosDeltaSq5mem : ∀ v : Fin 5 → ℝ, v ∈ PosDeltaSq5 ↔ 0 < (v 3)^2 - (v 4 - v 0)^2 := by
    intro v; rw [hPosDeltaSq5def]; exact inf_mem_slab4 v
  have hA5mem : ∀ v : Fin 5 → ℝ,
      v ∈ A5 ↔ (0 < (v 4 - v 0)^2 ∧ 0 < (v 3)^2 - (v 4 - v 0)^2) := by
    intro v; rw [hA5def]; simp only [Set.mem_inter_iff, Set.mem_ofPred_eq]
    rw [hPosYDiff5mem v, hPosDeltaSq5mem v]
  have hC6mem : ∀ v : Fin 6 → ℝ,
      v ∈ C6 ↔ 0 < s * (v 5 - v 1) * (v 4 - v 0) - v 2 * (v 4 - v 0)^2 := by
    intro v; rw [hC6def]; exact inf_mem_slab5 s v
  have hInner6mem : ∀ v : Fin 6 → ℝ, v ∈ Inner6 ↔ v ∈ GY6 ∧ v ∈ C6 := by
    intro v; rw [hInner6def]; simp only [Set.mem_inter_iff]
  have hBody5mem : ∀ w : Fin 5 → ℝ, w ∈ Body5 ↔ w ∈ A5 ∧ w ∉ Wire5 := by
    intro w; rw [hBody5def]; simp only [Set.mem_inter_iff, Set.mem_compl_iff]
  have hForallY4mem : ∀ u : Fin 4 → ℝ, u ∈ ForallY4 ↔ ∀ y, Fin.snoc u y ∉ Body5 := by
    intro u; rw [hForallY4def]
    simp only [Set.mem_compl_iff, projLast, Set.mem_ofPred_eq, not_exists]
  have hDelta4mem : ∀ u : Fin 4 → ℝ, u ∈ Delta4 ↔ 0 < u 3 ∧ ∀ y, Fin.snoc u y ∉ Body5 := by
    intro u; rw [hDelta4def]; simp only [Set.mem_inter_iff]
    rw [hPosDelta4mem u, hForallY4mem u]
  have hExDelta3mem : ∀ v : Fin 3 → ℝ, v ∈ ExDelta3 ↔ ∃ δ, Fin.snoc v δ ∈ Delta4 := by
    intro v; rw [hExDelta3def, projLast]; simp only [Set.mem_ofPred_eq]
  have hInner3mem : ∀ v : Fin 3 → ℝ, v ∈ Inner3 ↔ 1 < v 2 ∧ v ∉ ExDelta3 := by
    intro v; rw [hInner3def]; simp only [Set.mem_inter_iff, Set.mem_compl_iff]
    rw [hLtM3mem v]
  have hRest2mem : ∀ v : Fin 2 → ℝ, v ∈ Rest2 ↔ ∀ M, Fin.snoc v M ∉ Inner3 := by
    intro v; rw [hRest2def]
    simp only [Set.mem_compl_iff, projLast, Set.mem_ofPred_eq, not_exists]
  have hF2mem : ∀ v : Fin 2 → ℝ, v ∈ F2 ↔ v ∈ GX2 ∧ v ∈ Rest2 := by
    intro v; rw [hF2def]; simp only [Set.mem_inter_iff]
  have hWire5mem : ∀ w : Fin 5 → ℝ, w ∈ Wire5 ↔
      0 < s * (g (w 4) - w 1) * (w 4 - w 0) - w 2 * (w 4 - w 0)^2 := by
    intro w
    rw [hWire5def, projLast]; simp only [Set.mem_ofPred_eq]
    constructor
    · rintro ⟨t, ht⟩
      rw [hInner6mem] at ht
      obtain ⟨h1, h2⟩ := ht
      rw [hGY6mem] at h1
      rw [hC6mem] at h2
      have e5 : (Fin.snoc w t : Fin 6 → ℝ) (5:Fin 6) = t := rfl
      have e4 : (Fin.snoc w t : Fin 6 → ℝ) (4:Fin 6) = w 4 := rfl
      have e1 : (Fin.snoc w t : Fin 6 → ℝ) (1:Fin 6) = w 1 := rfl
      have e2 : (Fin.snoc w t : Fin 6 → ℝ) (2:Fin 6) = w 2 := rfl
      have e0 : (Fin.snoc w t : Fin 6 → ℝ) (0:Fin 6) = w 0 := rfl
      rw [e5, e4] at h1
      rw [e5, e4, e1, e2, e0] at h2
      rw [h1] at h2
      exact h2
    · intro h
      refine ⟨g (w 4), ?_⟩
      rw [hInner6mem]
      refine ⟨?_, ?_⟩
      · rw [hGY6mem]
        have e5 : (Fin.snoc w (g (w 4)) : Fin 6 → ℝ) (5:Fin 6) = g (w 4) := rfl
        have e4 : (Fin.snoc w (g (w 4)) : Fin 6 → ℝ) (4:Fin 6) = w 4 := rfl
        rw [e5, e4]
      · rw [hC6mem]
        have e5 : (Fin.snoc w (g (w 4)) : Fin 6 → ℝ) (5:Fin 6) = g (w 4) := rfl
        have e4 : (Fin.snoc w (g (w 4)) : Fin 6 → ℝ) (4:Fin 6) = w 4 := rfl
        have e1 : (Fin.snoc w (g (w 4)) : Fin 6 → ℝ) (1:Fin 6) = w 1 := rfl
        have e2 : (Fin.snoc w (g (w 4)) : Fin 6 → ℝ) (2:Fin 6) = w 2 := rfl
        have e0 : (Fin.snoc w (g (w 4)) : Fin 6 → ℝ) (0:Fin 6) = w 0 := rfl
        rw [e5, e4, e1, e2, e0]
        exact h
  -- The realised set is exactly `liftR (infDeriv g s)`.
  have hBeq : projLast F2 = Work.WilG1.liftR (Work.WilG1.infDeriv g s) := by
    ext z
    rw [Work.WilG1.liftR, Set.mem_ofPred_eq, projLast, Set.mem_ofPred_eq,
        Work.WilG1.infDeriv, Set.mem_ofPred_eq]
    constructor
    · rintro ⟨t, ht⟩
      rw [hF2mem] at ht
      obtain ⟨htG, htR⟩ := ht
      rw [hGX2mem] at htG
      have e1 : (Fin.snoc z t : Fin 2 → ℝ) 1 = t := rfl
      have e0 : (Fin.snoc z t : Fin 2 → ℝ) 0 = z 0 := rfl
      rw [e1, e0] at htG
      rw [hRest2mem] at htR
      rw [htG] at htR
      intro M hM
      set W2 : Fin 2 → ℝ := Fin.snoc z (g (z 0)) with hW2
      set W3 : Fin 3 → ℝ := Fin.snoc W2 M with hW3
      have hmem : W3 ∈ ExDelta3 := by
        by_contra hc
        refine htR M ((hInner3mem W3).mpr ⟨?_, hc⟩)
        have e2 : W3 2 = M := by rw [hW3]; rfl
        rw [e2]; exact hM
      rw [hExDelta3mem] at hmem
      obtain ⟨δ, hδ⟩ := hmem
      set W4 : Fin 4 → ℝ := Fin.snoc W3 δ with hW4
      rw [hDelta4mem] at hδ
      obtain ⟨hδpos, hδall⟩ := hδ
      have e3 : W4 3 = δ := by rw [hW4]; rfl
      rw [e3] at hδpos
      refine ⟨δ, hδpos, ?_⟩
      intro y hy1 hy2
      have hW5mem : Fin.snoc W4 y ∉ Body5 := hδall y
      have hW5A : Fin.snoc W4 y ∈ A5 := by
        rw [hA5mem]
        have e4 : (Fin.snoc W4 y : Fin 5 → ℝ) 4 = y := rfl
        have e0 : (Fin.snoc W4 y : Fin 5 → ℝ) 0 = z 0 := by rw [hW4, hW3, hW2]; rfl
        have e3 : (Fin.snoc W4 y : Fin 5 → ℝ) 3 = δ := by rw [hW4]; rfl
        rw [e4, e0, e3]
        exact (inf_aux_hyp hδpos).mpr ⟨hy1, hy2⟩
      have hW5W : Fin.snoc W4 y ∈ Wire5 := by
        by_contra hc
        exact hW5mem ((hBody5mem _).mpr ⟨hW5A, hc⟩)
      rw [hWire5mem] at hW5W
      have e4 : (Fin.snoc W4 y : Fin 5 → ℝ) 4 = y := rfl
      have e1 : (Fin.snoc W4 y : Fin 5 → ℝ) 1 = g (z 0) := by rw [hW4, hW3, hW2]; rfl
      have e0 : (Fin.snoc W4 y : Fin 5 → ℝ) 0 = z 0 := by rw [hW4, hW3, hW2]; rfl
      have e2 : (Fin.snoc W4 y : Fin 5 → ℝ) 2 = M := by rw [hW4, hW3]; rfl
      rw [e4, e1, e0, e2] at hW5W
      rw [Work.WilG1.dq]
      exact (inf_aux_ineq M s (g y - g (z 0)) (y - z 0) (sub_ne_zero.mpr hy1)).mp hW5W
    · intro hz
      refine ⟨g (z 0), ?_⟩
      set W2 : Fin 2 → ℝ := Fin.snoc z (g (z 0)) with hW2
      rw [hF2mem]
      refine ⟨?_, ?_⟩
      · rw [hGX2mem]
        have e1 : W2 1 = g (z 0) := by rw [hW2]; rfl
        have e0 : W2 0 = z 0 := by rw [hW2]; rfl
        rw [e1, e0]
      · rw [hRest2mem]
        intro M
        by_cases hM : 1 < M
        · set W3 : Fin 3 → ℝ := Fin.snoc W2 M with hW3
          obtain ⟨δ, hδpos, hδall⟩ := hz M hM
          have hmem : W3 ∈ ExDelta3 := by
            rw [hExDelta3mem]
            refine ⟨δ, ?_⟩
            set W4 : Fin 4 → ℝ := Fin.snoc W3 δ with hW4
            rw [hDelta4mem]
            refine ⟨?_, ?_⟩
            · have e3 : W4 3 = δ := by rw [hW4]; rfl
              rw [e3]; exact hδpos
            · intro y
              rw [hBody5mem]
              rintro ⟨hA, hW⟩
              have hA' : (0 < (y - z 0)^2 ∧ 0 < δ^2 - (y - z 0)^2) := by
                rw [hA5mem] at hA
                have e4 : (Fin.snoc W4 y : Fin 5 → ℝ) 4 = y := rfl
                have e0 : (Fin.snoc W4 y : Fin 5 → ℝ) 0 = z 0 := by rw [hW4, hW3, hW2]; rfl
                have e3 : (Fin.snoc W4 y : Fin 5 → ℝ) 3 = δ := by rw [hW4]; rfl
                rw [e4, e0, e3] at hA
                exact hA
              obtain ⟨hy1, hy2⟩ := (inf_aux_hyp hδpos).mp hA'
              have hdq : M < s * Work.WilG1.dq g (z 0) y := hδall y hy1 hy2
              rw [Work.WilG1.dq] at hdq
              have hineq : 0 < s * (g y - g (z 0)) * (y - z 0) - M * (y - z 0)^2 :=
                (inf_aux_ineq M s (g y - g (z 0)) (y - z 0) (sub_ne_zero.mpr hy1)).mpr hdq
              rw [hWire5mem] at hW
              have e4 : (Fin.snoc W4 y : Fin 5 → ℝ) 4 = y := rfl
              have e1 : (Fin.snoc W4 y : Fin 5 → ℝ) 1 = g (z 0) := by rw [hW4, hW3, hW2]; rfl
              have e0 : (Fin.snoc W4 y : Fin 5 → ℝ) 0 = z 0 := by rw [hW4, hW3, hW2]; rfl
              have e2 : (Fin.snoc W4 y : Fin 5 → ℝ) 2 = M := by rw [hW4, hW3]; rfl
              rw [e4, e1, e0, e2] at hW
              exact hW hineq
          rw [hInner3mem]
          rintro ⟨-, hc⟩
          exact hc hmem
        · rw [hInner3mem]
          have e2 : (Fin.snoc W2 M : Fin 3 → ℝ) 2 = M := rfl
          rw [e2]
          rintro ⟨h1, _⟩
          exact absurd h1 hM
  -- Assemble: pad the format and the degree of the explicit membership.
  have hfin : Work.WilG1.liftR (Work.WilG1.infDeriv g s) ∈
      S.Ω (F+31) ((D+2) + (3 + (3 + (8 + ((D+2)+5))))) 1 := by
    rw [← hBeq]
    exact hB
  refine Work.WilG0.Omega_mono_FD (by omega) ?_ hfin
  simp only [Polynomial.eval_mul, Polynomial.eval_add, Polynomial.eval_C, Polynomial.eval_X]
  omega

end Work.WilG1.OneDim
