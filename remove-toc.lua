-- From ChatGTP, admittedly...

function Pandoc(doc)
    local new_blocks = {}
    local removing_toc = false

    for _, block in ipairs(doc.blocks) do

        if block.t == "Header" then
            local title = pandoc.utils.stringify(block.content)

            -- Start removing at "Table of contents"
            if title == "Table of contents" and block.level == 4 then
                removing_toc = true
            -- Stop when we reach the next heading of level 4 or higher
            elseif removing_toc and block.level <= 4 then
                removing_toc = false
            end
        end

        if not removing_toc then
            table.insert(new_blocks, block)
        end
    end

    doc.blocks = new_blocks
    return doc
end